%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:30 EST 2020

% Result     : Theorem 44.14s
% Output     : Refutation 44.14s
% Verified   : 
% Statistics : Number of formulae       :  866 (10535 expanded)
%              Number of leaves         :  168 (2960 expanded)
%              Depth                    :   31
%              Number of atoms          : 2145 (51267 expanded)
%              Number of equality atoms :  592 (12480 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f144730,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f101,f110,f115,f181,f3245,f3271,f3323,f3896,f3924,f4047,f4175,f4272,f4366,f5828,f5866,f5926,f5991,f6285,f6742,f6782,f6924,f6995,f7445,f7808,f7857,f7864,f7935,f7979,f9047,f9092,f9153,f10219,f10906,f11021,f11054,f11119,f11176,f11443,f11557,f11667,f13292,f13389,f14839,f14938,f15093,f15620,f52879,f52886,f52891,f52976,f53034,f55677,f56522,f56543,f60573,f60580,f60585,f62746,f66307,f67303,f69554,f69624,f69718,f70369,f75656,f76269,f76274,f76279,f77183,f78251,f78258,f79656,f79678,f81049,f81063,f81066,f81293,f81300,f81305,f81458,f81581,f81637,f81638,f81643,f81748,f82952,f82957,f82972,f83073,f83168,f83327,f83349,f85173,f89398,f90288,f93954,f94893,f94898,f95094,f95099,f96457,f96473,f96580,f96680,f96696,f97204,f97209,f98046,f98051,f98055,f98060,f98577,f98581,f98586,f102128,f105943,f116207,f116736,f116743,f117252,f117401,f117408,f117413,f117426,f117441,f117828,f118016,f118920,f118934,f121507,f121982,f122820,f126346,f126950,f127795,f127800,f128301,f128605,f128610,f129047,f129050,f129083,f129088,f129486,f129616,f129684,f129755,f129824,f131409,f134281,f135202,f136503,f139264,f139300,f139431,f139464,f139469,f144307,f144343,f144710,f144722])).

fof(f144722,plain,(
    ~ spl9_149 ),
    inference(avatar_contradiction_clause,[],[f144711])).

fof(f144711,plain,
    ( $false
    | ~ spl9_149 ),
    inference(resolution,[],[f144709,f123])).

fof(f123,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f121,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f121,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X0))) ),
    inference(resolution,[],[f86,f81])).

fof(f81,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f86,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK7(X0,X1,X2),X1)
            | ~ r2_hidden(sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
              & r2_hidden(sK7(X0,X1,X2),X0) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK7(X0,X1,X2),X1)
          | ~ r2_hidden(sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
            & r2_hidden(sK7(X0,X1,X2),X0) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f144709,plain,
    ( r2_hidden(sK6(sK2,sK0),k1_xboole_0)
    | ~ spl9_149 ),
    inference(avatar_component_clause,[],[f144707])).

fof(f144707,plain,
    ( spl9_149
  <=> r2_hidden(sK6(sK2,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_149])])).

fof(f144710,plain,
    ( spl9_149
    | ~ spl9_17
    | ~ spl9_140
    | ~ spl9_147 ),
    inference(avatar_split_clause,[],[f144610,f144304,f135199,f5924,f144707])).

fof(f5924,plain,
    ( spl9_17
  <=> ! [X8] : k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X8,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f135199,plain,
    ( spl9_140
  <=> r2_hidden(sK6(sK2,sK0),k3_xboole_0(sK0,k1_tarski(sK6(sK2,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_140])])).

fof(f144304,plain,
    ( spl9_147
  <=> k1_tarski(sK6(sK2,sK0)) = k4_xboole_0(k1_tarski(sK6(sK2,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_147])])).

fof(f144610,plain,
    ( r2_hidden(sK6(sK2,sK0),k1_xboole_0)
    | ~ spl9_17
    | ~ spl9_140
    | ~ spl9_147 ),
    inference(backward_demodulation,[],[f135201,f144529])).

fof(f144529,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK6(sK2,sK0)))
    | ~ spl9_17
    | ~ spl9_147 ),
    inference(superposition,[],[f5925,f144306])).

fof(f144306,plain,
    ( k1_tarski(sK6(sK2,sK0)) = k4_xboole_0(k1_tarski(sK6(sK2,sK0)),sK2)
    | ~ spl9_147 ),
    inference(avatar_component_clause,[],[f144304])).

fof(f5925,plain,
    ( ! [X8] : k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X8,sK2))
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f5924])).

fof(f135201,plain,
    ( r2_hidden(sK6(sK2,sK0),k3_xboole_0(sK0,k1_tarski(sK6(sK2,sK0))))
    | ~ spl9_140 ),
    inference(avatar_component_clause,[],[f135199])).

fof(f144343,plain,
    ( spl9_7
    | ~ spl9_148
    | ~ spl9_129 ),
    inference(avatar_split_clause,[],[f129024,f128607,f144340,f174])).

fof(f174,plain,
    ( spl9_7
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f144340,plain,
    ( spl9_148
  <=> r2_hidden(sK6(k1_xboole_0,sK2),k1_tarski(sK6(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_148])])).

fof(f128607,plain,
    ( spl9_129
  <=> sK2 = k4_xboole_0(sK2,k1_tarski(sK6(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_129])])).

fof(f129024,plain,
    ( ~ r2_hidden(sK6(k1_xboole_0,sK2),k1_tarski(sK6(sK2,sK0)))
    | k1_xboole_0 = sK2
    | ~ spl9_129 ),
    inference(superposition,[],[f95608,f128609])).

fof(f128609,plain,
    ( sK2 = k4_xboole_0(sK2,k1_tarski(sK6(sK2,sK0)))
    | ~ spl9_129 ),
    inference(avatar_component_clause,[],[f128607])).

fof(f95608,plain,(
    ! [X14,X13] :
      ( ~ r2_hidden(sK6(k1_xboole_0,k4_xboole_0(X14,X13)),X13)
      | k1_xboole_0 = k4_xboole_0(X14,X13) ) ),
    inference(superposition,[],[f152,f95320])).

fof(f95320,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2 ),
    inference(superposition,[],[f84371,f226])).

fof(f226,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f223,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f223,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k3_xboole_0(k4_xboole_0(X2,X3),X2) ),
    inference(resolution,[],[f220,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f220,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(duplicate_literal_removal,[],[f208])).

fof(f208,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X0)
      | r1_tarski(k4_xboole_0(X0,X1),X0) ) ),
    inference(resolution,[],[f134,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(k4_xboole_0(X0,X1),X2),X0)
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f87,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f84371,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2))) = X2 ),
    inference(resolution,[],[f84352,f54])).

fof(f84352,plain,(
    ! [X2,X3] : r1_tarski(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2))) ),
    inference(duplicate_literal_removal,[],[f84284])).

fof(f84284,plain,(
    ! [X2,X3] :
      ( r1_tarski(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2)))
      | r1_tarski(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2))) ) ),
    inference(resolution,[],[f83321,f122])).

fof(f122,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(sK4(X2,X3),k4_xboole_0(X4,X2))
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f86,f56])).

fof(f83321,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK4(X4,k4_xboole_0(X4,X5)),X5)
      | r1_tarski(X4,k4_xboole_0(X4,X5)) ) ),
    inference(duplicate_literal_removal,[],[f83261])).

fof(f83261,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK4(X4,k4_xboole_0(X4,X5)),X5)
      | r1_tarski(X4,k4_xboole_0(X4,X5))
      | r1_tarski(X4,k4_xboole_0(X4,X5)) ) ),
    inference(resolution,[],[f183,f57])).

fof(f183,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK4(X2,X3),k4_xboole_0(X2,X4))
      | r2_hidden(sK4(X2,X3),X4)
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f85,f56])).

fof(f85,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X0)
      | r2_hidden(X4,X1)
      | r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(k1_xboole_0,X0),k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f151,f86])).

fof(f151,plain,(
    ! [X1] :
      ( r2_hidden(sK6(k1_xboole_0,X1),X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f149,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK6(X0,X1),X0)
        & r2_hidden(sK6(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK6(X0,X1),X0)
        & r2_hidden(sK6(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f149,plain,(
    ! [X1] :
      ( r2_xboole_0(k1_xboole_0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f55,f124])).

fof(f124,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f123,f56])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f144307,plain,
    ( spl9_147
    | ~ spl9_129 ),
    inference(avatar_split_clause,[],[f129021,f128607,f144304])).

fof(f129021,plain,
    ( k1_tarski(sK6(sK2,sK0)) = k4_xboole_0(k1_tarski(sK6(sK2,sK0)),sK2)
    | ~ spl9_129 ),
    inference(superposition,[],[f95320,f128609])).

fof(f139469,plain,
    ( spl9_146
    | spl9_143 ),
    inference(avatar_split_clause,[],[f139314,f139297,f139466])).

fof(f139466,plain,
    ( spl9_146
  <=> k1_xboole_0 = k3_xboole_0(k1_tarski(sK6(sK1,sK1)),k1_tarski(sK6(k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_146])])).

fof(f139297,plain,
    ( spl9_143
  <=> r2_hidden(sK6(k1_xboole_0,sK1),k1_tarski(sK6(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_143])])).

fof(f139314,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_tarski(sK6(sK1,sK1)),k1_tarski(sK6(k1_xboole_0,sK1)))
    | spl9_143 ),
    inference(resolution,[],[f139299,f1331])).

fof(f1331,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_xboole_0 = k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(resolution,[],[f1300,f90])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
            | ~ r2_hidden(sK8(X0,X1,X2),X0)
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK8(X0,X1,X2),X1)
              & r2_hidden(sK8(X0,X1,X2),X0) )
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f44,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
          | ~ r2_hidden(sK8(X0,X1,X2),X0)
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK8(X0,X1,X2),X1)
            & r2_hidden(sK8(X0,X1,X2),X0) )
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f1300,plain,(
    ! [X12,X13] :
      ( r2_hidden(X12,k3_xboole_0(X13,k1_tarski(X12)))
      | k1_xboole_0 = k3_xboole_0(X13,k1_tarski(X12)) ) ),
    inference(superposition,[],[f966,f53])).

fof(f966,plain,(
    ! [X8,X7] :
      ( r2_hidden(X7,k3_xboole_0(k1_tarski(X7),X8))
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X7),X8) ) ),
    inference(forward_demodulation,[],[f965,f309])).

fof(f309,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k3_xboole_0(X3,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f273,f53])).

fof(f273,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),X2) ),
    inference(resolution,[],[f266,f54])).

fof(f266,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f261,f53])).

fof(f261,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X1) ),
    inference(duplicate_literal_removal,[],[f243])).

fof(f243,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X1),X1)
      | r1_tarski(k3_xboole_0(X0,X1),X1) ) ),
    inference(resolution,[],[f136,f57])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(k3_xboole_0(X0,X1),X2),X1)
      | r1_tarski(k3_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f89,f56])).

fof(f89,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f965,plain,(
    ! [X8,X7] :
      ( r2_hidden(X7,k3_xboole_0(k1_tarski(X7),k3_xboole_0(k1_tarski(X7),X8)))
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X7),X8) ) ),
    inference(forward_demodulation,[],[f961,f53])).

fof(f961,plain,(
    ! [X8,X7] :
      ( r2_hidden(X7,k3_xboole_0(k3_xboole_0(k1_tarski(X7),X8),k1_tarski(X7)))
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X7),X8) ) ),
    inference(duplicate_literal_removal,[],[f956])).

fof(f956,plain,(
    ! [X8,X7] :
      ( r2_hidden(X7,k3_xboole_0(k3_xboole_0(k1_tarski(X7),X8),k1_tarski(X7)))
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X7),X8)
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X7),X8) ) ),
    inference(superposition,[],[f199,f473])).

fof(f473,plain,(
    ! [X24,X23] :
      ( sK6(k1_xboole_0,k3_xboole_0(k1_tarski(X23),X24)) = X23
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X23),X24) ) ),
    inference(resolution,[],[f153,f82])).

fof(f82,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f153,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK6(k1_xboole_0,k3_xboole_0(X2,X3)),X2)
      | k1_xboole_0 = k3_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f151,f90])).

fof(f199,plain,(
    ! [X5] :
      ( r2_hidden(sK6(k1_xboole_0,X5),k3_xboole_0(X5,k1_tarski(sK6(k1_xboole_0,X5))))
      | k1_xboole_0 = X5 ) ),
    inference(resolution,[],[f192,f151])).

fof(f192,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(X0,k3_xboole_0(X1,k1_tarski(X0))) ) ),
    inference(resolution,[],[f88,f81])).

fof(f88,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f139299,plain,
    ( ~ r2_hidden(sK6(k1_xboole_0,sK1),k1_tarski(sK6(sK1,sK1)))
    | spl9_143 ),
    inference(avatar_component_clause,[],[f139297])).

fof(f139464,plain,
    ( spl9_145
    | spl9_143 ),
    inference(avatar_split_clause,[],[f139301,f139297,f139461])).

fof(f139461,plain,
    ( spl9_145
  <=> k1_xboole_0 = k3_xboole_0(k1_tarski(sK6(k1_xboole_0,sK1)),k1_tarski(sK6(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_145])])).

fof(f139301,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_tarski(sK6(k1_xboole_0,sK1)),k1_tarski(sK6(sK1,sK1)))
    | spl9_143 ),
    inference(resolution,[],[f139299,f963])).

fof(f963,plain,(
    ! [X4,X3] :
      ( r2_hidden(X3,X4)
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X3),X4) ) ),
    inference(duplicate_literal_removal,[],[f954])).

fof(f954,plain,(
    ! [X4,X3] :
      ( r2_hidden(X3,X4)
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X3),X4)
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X3),X4) ) ),
    inference(superposition,[],[f154,f473])).

fof(f154,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK6(k1_xboole_0,k3_xboole_0(X4,X5)),X5)
      | k1_xboole_0 = k3_xboole_0(X4,X5) ) ),
    inference(resolution,[],[f151,f89])).

fof(f139431,plain,
    ( ~ spl9_144
    | ~ spl9_97
    | ~ spl9_142 ),
    inference(avatar_split_clause,[],[f139344,f139261,f96470,f139428])).

fof(f139428,plain,
    ( spl9_144
  <=> r2_hidden(sK4(sK1,k1_xboole_0),k1_tarski(sK6(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_144])])).

fof(f96470,plain,
    ( spl9_97
  <=> r2_hidden(sK4(sK1,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_97])])).

fof(f139261,plain,
    ( spl9_142
  <=> k1_tarski(sK6(sK1,sK1)) = k4_xboole_0(k1_tarski(sK6(sK1,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_142])])).

fof(f139344,plain,
    ( ~ r2_hidden(sK4(sK1,k1_xboole_0),k1_tarski(sK6(sK1,sK1)))
    | ~ spl9_97
    | ~ spl9_142 ),
    inference(superposition,[],[f96475,f139263])).

fof(f139263,plain,
    ( k1_tarski(sK6(sK1,sK1)) = k4_xboole_0(k1_tarski(sK6(sK1,sK1)),sK1)
    | ~ spl9_142 ),
    inference(avatar_component_clause,[],[f139261])).

fof(f96475,plain,
    ( ! [X1] : ~ r2_hidden(sK4(sK1,k1_xboole_0),k4_xboole_0(X1,sK1))
    | ~ spl9_97 ),
    inference(resolution,[],[f96472,f86])).

fof(f96472,plain,
    ( r2_hidden(sK4(sK1,k1_xboole_0),sK1)
    | ~ spl9_97 ),
    inference(avatar_component_clause,[],[f96470])).

fof(f139300,plain,
    ( spl9_2
    | ~ spl9_143
    | ~ spl9_133 ),
    inference(avatar_split_clause,[],[f129587,f129483,f139297,f98])).

fof(f98,plain,
    ( spl9_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f129483,plain,
    ( spl9_133
  <=> sK1 = k4_xboole_0(sK1,k1_tarski(sK6(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_133])])).

fof(f129587,plain,
    ( ~ r2_hidden(sK6(k1_xboole_0,sK1),k1_tarski(sK6(sK1,sK1)))
    | k1_xboole_0 = sK1
    | ~ spl9_133 ),
    inference(superposition,[],[f95608,f129485])).

fof(f129485,plain,
    ( sK1 = k4_xboole_0(sK1,k1_tarski(sK6(sK1,sK1)))
    | ~ spl9_133 ),
    inference(avatar_component_clause,[],[f129483])).

fof(f139264,plain,
    ( spl9_142
    | ~ spl9_133 ),
    inference(avatar_split_clause,[],[f129584,f129483,f139261])).

fof(f129584,plain,
    ( k1_tarski(sK6(sK1,sK1)) = k4_xboole_0(k1_tarski(sK6(sK1,sK1)),sK1)
    | ~ spl9_133 ),
    inference(superposition,[],[f95320,f129485])).

fof(f136503,plain,
    ( spl9_141
    | ~ spl9_124 ),
    inference(avatar_split_clause,[],[f126956,f126947,f136500])).

fof(f136500,plain,
    ( spl9_141
  <=> r2_hidden(sK4(sK0,k1_xboole_0),k3_xboole_0(sK0,k1_tarski(sK4(sK0,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_141])])).

fof(f126947,plain,
    ( spl9_124
  <=> r2_hidden(sK4(sK0,k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_124])])).

fof(f126956,plain,
    ( r2_hidden(sK4(sK0,k1_xboole_0),k3_xboole_0(sK0,k1_tarski(sK4(sK0,k1_xboole_0))))
    | ~ spl9_124 ),
    inference(resolution,[],[f126949,f192])).

fof(f126949,plain,
    ( r2_hidden(sK4(sK0,k1_xboole_0),sK0)
    | ~ spl9_124 ),
    inference(avatar_component_clause,[],[f126947])).

fof(f135202,plain,
    ( spl9_140
    | ~ spl9_77 ),
    inference(avatar_split_clause,[],[f119015,f81302,f135199])).

fof(f81302,plain,
    ( spl9_77
  <=> r2_hidden(sK6(sK2,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_77])])).

fof(f119015,plain,
    ( r2_hidden(sK6(sK2,sK0),k3_xboole_0(sK0,k1_tarski(sK6(sK2,sK0))))
    | ~ spl9_77 ),
    inference(forward_demodulation,[],[f81341,f84413])).

fof(f84413,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(superposition,[],[f84358,f226])).

fof(f84358,plain,(
    ! [X1] : k3_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(resolution,[],[f84309,f54])).

fof(f84309,plain,(
    ! [X76] : r1_tarski(X76,k4_xboole_0(X76,k1_xboole_0)) ),
    inference(resolution,[],[f83321,f123])).

fof(f81341,plain,
    ( r2_hidden(sK6(sK2,sK0),k3_xboole_0(sK0,k4_xboole_0(k1_tarski(sK6(sK2,sK0)),k1_xboole_0)))
    | ~ spl9_77 ),
    inference(resolution,[],[f81304,f2127])).

fof(f2127,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X8,X9)
      | r2_hidden(X8,k3_xboole_0(X9,k4_xboole_0(k1_tarski(X8),k1_xboole_0))) ) ),
    inference(resolution,[],[f2026,f88])).

fof(f2026,plain,(
    ! [X0] : r2_hidden(X0,k4_xboole_0(k1_tarski(X0),k1_xboole_0)) ),
    inference(superposition,[],[f2014,f51])).

fof(f2014,plain,(
    ! [X0,X1] : r2_hidden(X0,k4_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0)))) ),
    inference(global_subsumption,[],[f123,f1984])).

fof(f1984,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_xboole_0)
      | r2_hidden(X0,k4_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0)))) ) ),
    inference(superposition,[],[f182,f1896])).

fof(f1896,plain,(
    ! [X24,X25] : k1_xboole_0 = k4_xboole_0(k1_tarski(X24),k4_xboole_0(k1_tarski(X24),k4_xboole_0(X25,k1_tarski(X24)))) ),
    inference(resolution,[],[f1629,f121])).

fof(f1629,plain,(
    ! [X8,X7] :
      ( r2_hidden(X7,X8)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X7),k4_xboole_0(k1_tarski(X7),X8)) ) ),
    inference(resolution,[],[f1304,f188])).

fof(f188,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X6,k4_xboole_0(X8,k4_xboole_0(k1_tarski(X6),X7)))
      | r2_hidden(X6,X7) ) ),
    inference(resolution,[],[f182,f86])).

fof(f1304,plain,(
    ! [X21,X20] :
      ( r2_hidden(X20,k4_xboole_0(k1_tarski(X20),X21))
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X20),X21) ) ),
    inference(superposition,[],[f966,f226])).

fof(f182,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(k1_tarski(X0),X1))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f85,f81])).

fof(f81304,plain,
    ( r2_hidden(sK6(sK2,sK0),sK0)
    | ~ spl9_77 ),
    inference(avatar_component_clause,[],[f81302])).

fof(f134281,plain,
    ( spl9_139
    | ~ spl9_78 ),
    inference(avatar_split_clause,[],[f119013,f81578,f134278])).

fof(f134278,plain,
    ( spl9_139
  <=> r2_hidden(sK6(k1_xboole_0,sK2),k3_xboole_0(sK0,k1_tarski(sK6(k1_xboole_0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_139])])).

fof(f81578,plain,
    ( spl9_78
  <=> r2_hidden(sK6(k1_xboole_0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_78])])).

fof(f119013,plain,
    ( r2_hidden(sK6(k1_xboole_0,sK2),k3_xboole_0(sK0,k1_tarski(sK6(k1_xboole_0,sK2))))
    | ~ spl9_78 ),
    inference(forward_demodulation,[],[f81589,f84413])).

fof(f81589,plain,
    ( r2_hidden(sK6(k1_xboole_0,sK2),k3_xboole_0(sK0,k4_xboole_0(k1_tarski(sK6(k1_xboole_0,sK2)),k1_xboole_0)))
    | ~ spl9_78 ),
    inference(resolution,[],[f81580,f2127])).

fof(f81580,plain,
    ( r2_hidden(sK6(k1_xboole_0,sK2),sK0)
    | ~ spl9_78 ),
    inference(avatar_component_clause,[],[f81578])).

fof(f131409,plain,
    ( spl9_138
    | ~ spl9_123 ),
    inference(avatar_split_clause,[],[f126559,f122817,f131406])).

fof(f131406,plain,
    ( spl9_138
  <=> r2_hidden(sK4(sK0,k1_xboole_0),k3_xboole_0(sK2,k1_tarski(sK4(sK0,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_138])])).

fof(f122817,plain,
    ( spl9_123
  <=> r2_hidden(sK4(sK0,k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_123])])).

fof(f126559,plain,
    ( r2_hidden(sK4(sK0,k1_xboole_0),k3_xboole_0(sK2,k1_tarski(sK4(sK0,k1_xboole_0))))
    | ~ spl9_123 ),
    inference(resolution,[],[f122819,f192])).

fof(f122819,plain,
    ( r2_hidden(sK4(sK0,k1_xboole_0),sK2)
    | ~ spl9_123 ),
    inference(avatar_component_clause,[],[f122817])).

fof(f129824,plain,
    ( spl9_7
    | spl9_137
    | ~ spl9_73 ),
    inference(avatar_split_clause,[],[f80977,f78248,f129822,f174])).

fof(f129822,plain,
    ( spl9_137
  <=> ! [X111] : r2_hidden(sK8(X111,k1_xboole_0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_137])])).

fof(f78248,plain,
    ( spl9_73
  <=> sK2 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_73])])).

fof(f80977,plain,
    ( ! [X111] :
        ( r2_hidden(sK8(X111,k1_xboole_0,sK2),sK0)
        | k1_xboole_0 = sK2 )
    | ~ spl9_73 ),
    inference(superposition,[],[f41943,f78250])).

fof(f78250,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | ~ spl9_73 ),
    inference(avatar_component_clause,[],[f78248])).

fof(f41943,plain,(
    ! [X24,X23,X22] :
      ( r2_hidden(sK8(X24,k1_xboole_0,k3_xboole_0(X22,X23)),X22)
      | k1_xboole_0 = k3_xboole_0(X22,X23) ) ),
    inference(resolution,[],[f41931,f90])).

fof(f41931,plain,(
    ! [X90,X91] :
      ( r2_hidden(sK8(X90,k1_xboole_0,X91),X91)
      | k1_xboole_0 = X91 ) ),
    inference(forward_demodulation,[],[f41871,f126])).

fof(f126,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f125,f53])).

fof(f125,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f124,f54])).

fof(f41871,plain,(
    ! [X90,X91] :
      ( r2_hidden(sK8(X90,k1_xboole_0,X91),X91)
      | k3_xboole_0(X90,k1_xboole_0) = X91 ) ),
    inference(resolution,[],[f77,f123])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),X1)
      | r2_hidden(sK8(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f129755,plain,
    ( spl9_7
    | spl9_136
    | ~ spl9_73 ),
    inference(avatar_split_clause,[],[f80973,f78248,f129753,f174])).

fof(f129753,plain,
    ( spl9_136
  <=> ! [X107] : r2_hidden(sK8(k1_xboole_0,X107,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_136])])).

fof(f80973,plain,
    ( ! [X107] :
        ( r2_hidden(sK8(k1_xboole_0,X107,sK2),sK0)
        | k1_xboole_0 = sK2 )
    | ~ spl9_73 ),
    inference(superposition,[],[f21863,f78250])).

fof(f21863,plain,(
    ! [X21,X22,X20] :
      ( r2_hidden(sK8(k1_xboole_0,X22,k3_xboole_0(X20,X21)),X20)
      | k1_xboole_0 = k3_xboole_0(X20,X21) ) ),
    inference(resolution,[],[f21852,f90])).

fof(f21852,plain,(
    ! [X52,X51] :
      ( r2_hidden(sK8(k1_xboole_0,X51,X52),X52)
      | k1_xboole_0 = X52 ) ),
    inference(forward_demodulation,[],[f21807,f125])).

fof(f21807,plain,(
    ! [X52,X51] :
      ( r2_hidden(sK8(k1_xboole_0,X51,X52),X52)
      | k3_xboole_0(k1_xboole_0,X51) = X52 ) ),
    inference(resolution,[],[f76,f123])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),X0)
      | r2_hidden(sK8(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f129684,plain,
    ( spl9_7
    | spl9_135
    | ~ spl9_73 ),
    inference(avatar_split_clause,[],[f80949,f78248,f129682,f174])).

fof(f129682,plain,
    ( spl9_135
  <=> ! [X59] : r2_hidden(sK7(X59,X59,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_135])])).

fof(f80949,plain,
    ( ! [X59] :
        ( r2_hidden(sK7(X59,X59,sK2),sK0)
        | k1_xboole_0 = sK2 )
    | ~ spl9_73 ),
    inference(superposition,[],[f11528,f78250])).

fof(f11528,plain,(
    ! [X23,X21,X22] :
      ( r2_hidden(sK7(X23,X23,k3_xboole_0(X21,X22)),X21)
      | k1_xboole_0 = k3_xboole_0(X21,X22) ) ),
    inference(resolution,[],[f11517,f90])).

fof(f11517,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X0,X1),X1)
      | k1_xboole_0 = X1 ) ),
    inference(forward_demodulation,[],[f11516,f608])).

fof(f608,plain,(
    ! [X14] : k1_xboole_0 = k4_xboole_0(X14,X14) ),
    inference(superposition,[],[f600,f126])).

fof(f600,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X2) = k3_xboole_0(k4_xboole_0(X2,X2),X3) ),
    inference(resolution,[],[f598,f54])).

fof(f598,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X0),X1) ),
    inference(duplicate_literal_removal,[],[f592])).

fof(f592,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X0),X1)
      | r1_tarski(k4_xboole_0(X0,X0),X1) ) ),
    inference(resolution,[],[f213,f56])).

fof(f213,plain,(
    ! [X19,X17,X18,X16] :
      ( ~ r2_hidden(sK4(k4_xboole_0(X16,X17),X18),k4_xboole_0(X19,X16))
      | r1_tarski(k4_xboole_0(X16,X17),X18) ) ),
    inference(resolution,[],[f134,f86])).

fof(f11516,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X0) = X1
      | r2_hidden(sK7(X0,X0,X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f11498])).

fof(f11498,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X0) = X1
      | r2_hidden(sK7(X0,X0,X1),X1)
      | r2_hidden(sK7(X0,X0,X1),X1)
      | k4_xboole_0(X0,X0) = X1 ) ),
    inference(resolution,[],[f71,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X0)
      | r2_hidden(sK7(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1,X2),X1)
      | k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK7(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f129616,plain,
    ( spl9_7
    | spl9_134
    | ~ spl9_73 ),
    inference(avatar_split_clause,[],[f80947,f78248,f129614,f174])).

fof(f129614,plain,
    ( spl9_134
  <=> ! [X57] : r2_hidden(sK7(k1_xboole_0,X57,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_134])])).

fof(f80947,plain,
    ( ! [X57] :
        ( r2_hidden(sK7(k1_xboole_0,X57,sK2),sK0)
        | k1_xboole_0 = sK2 )
    | ~ spl9_73 ),
    inference(superposition,[],[f6903,f78250])).

fof(f6903,plain,(
    ! [X21,X22,X20] :
      ( r2_hidden(sK7(k1_xboole_0,X22,k3_xboole_0(X20,X21)),X20)
      | k1_xboole_0 = k3_xboole_0(X20,X21) ) ),
    inference(resolution,[],[f6848,f90])).

fof(f6848,plain,(
    ! [X52,X51] :
      ( r2_hidden(sK7(k1_xboole_0,X51,X52),X52)
      | k1_xboole_0 = X52 ) ),
    inference(forward_demodulation,[],[f6809,f51])).

fof(f6809,plain,(
    ! [X52,X51] :
      ( r2_hidden(sK7(k1_xboole_0,X51,X52),X52)
      | k4_xboole_0(k1_xboole_0,X51) = X52 ) ),
    inference(resolution,[],[f70,f123])).

fof(f129486,plain,
    ( spl9_133
    | spl9_121 ),
    inference(avatar_split_clause,[],[f129078,f121979,f129483])).

fof(f121979,plain,
    ( spl9_121
  <=> r2_hidden(sK6(sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_121])])).

fof(f129078,plain,
    ( sK1 = k4_xboole_0(sK1,k1_tarski(sK6(sK1,sK1)))
    | spl9_121 ),
    inference(resolution,[],[f121980,f111163])).

fof(f111163,plain,(
    ! [X4,X3] :
      ( r2_hidden(X3,X4)
      | k4_xboole_0(X4,k1_tarski(X3)) = X4 ) ),
    inference(global_subsumption,[],[f123,f110963])).

fof(f110963,plain,(
    ! [X4,X3] :
      ( r2_hidden(X3,k1_xboole_0)
      | r2_hidden(X3,X4)
      | k4_xboole_0(X4,k1_tarski(X3)) = X4 ) ),
    inference(superposition,[],[f182,f95580])).

fof(f95580,plain,(
    ! [X6,X5] :
      ( k4_xboole_0(X6,k1_tarski(X5)) = X6
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X5),X6) ) ),
    inference(superposition,[],[f95320,f41576])).

fof(f41576,plain,(
    ! [X74,X73] :
      ( k1_tarski(X73) = k4_xboole_0(k1_tarski(X73),X74)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X73),X74) ) ),
    inference(superposition,[],[f39742,f226])).

fof(f39742,plain,(
    ! [X6,X5] :
      ( k1_tarski(X6) = k3_xboole_0(k1_tarski(X6),X5)
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X6),X5) ) ),
    inference(superposition,[],[f36640,f53])).

fof(f36640,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k3_xboole_0(X1,k1_tarski(X0))
      | k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f36461])).

fof(f36461,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k3_xboole_0(X1,k1_tarski(X0))
      | k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
      | k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) ) ),
    inference(superposition,[],[f1141,f159])).

fof(f159,plain,(
    ! [X2,X3] :
      ( sK4(k1_tarski(X2),X3) = X2
      | k1_tarski(X2) = k3_xboole_0(k1_tarski(X2),X3) ) ),
    inference(resolution,[],[f117,f54])).

fof(f117,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | sK4(k1_tarski(X0),X1) = X0 ) ),
    inference(resolution,[],[f56,f82])).

fof(f1141,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = k3_xboole_0(X2,k1_tarski(sK4(X3,X2)))
      | k3_xboole_0(X3,X2) = X3 ) ),
    inference(resolution,[],[f994,f54])).

fof(f994,plain,(
    ! [X35,X36] :
      ( r1_tarski(X35,X36)
      | k1_xboole_0 = k3_xboole_0(X36,k1_tarski(sK4(X35,X36))) ) ),
    inference(forward_demodulation,[],[f981,f53])).

fof(f981,plain,(
    ! [X35,X36] :
      ( k1_xboole_0 = k3_xboole_0(k1_tarski(sK4(X35,X36)),X36)
      | r1_tarski(X35,X36) ) ),
    inference(resolution,[],[f963,f57])).

fof(f121980,plain,
    ( ~ r2_hidden(sK6(sK1,sK1),sK1)
    | spl9_121 ),
    inference(avatar_component_clause,[],[f121979])).

fof(f129088,plain,
    ( spl9_132
    | spl9_121 ),
    inference(avatar_split_clause,[],[f129064,f121979,f129085])).

fof(f129085,plain,
    ( spl9_132
  <=> k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK6(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_132])])).

fof(f129064,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK6(sK1,sK1)))
    | spl9_121 ),
    inference(resolution,[],[f121980,f1331])).

fof(f129083,plain,
    ( spl9_131
    | spl9_121 ),
    inference(avatar_split_clause,[],[f129051,f121979,f129080])).

fof(f129080,plain,
    ( spl9_131
  <=> k1_xboole_0 = k3_xboole_0(k1_tarski(sK6(sK1,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_131])])).

fof(f129051,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_tarski(sK6(sK1,sK1)),sK1)
    | spl9_121 ),
    inference(resolution,[],[f121980,f963])).

fof(f129050,plain,
    ( ~ spl9_121
    | ~ spl9_4
    | spl9_118 ),
    inference(avatar_split_clause,[],[f129048,f117410,f107,f121979])).

fof(f107,plain,
    ( spl9_4
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f117410,plain,
    ( spl9_118
  <=> r2_hidden(sK6(sK3,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_118])])).

fof(f129048,plain,
    ( ~ r2_hidden(sK6(sK1,sK1),sK1)
    | ~ spl9_4
    | spl9_118 ),
    inference(forward_demodulation,[],[f117411,f108])).

fof(f108,plain,
    ( sK1 = sK3
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f117411,plain,
    ( ~ r2_hidden(sK6(sK3,sK1),sK1)
    | spl9_118 ),
    inference(avatar_component_clause,[],[f117410])).

fof(f129047,plain,
    ( spl9_130
    | ~ spl9_4
    | ~ spl9_118 ),
    inference(avatar_split_clause,[],[f120776,f117410,f107,f129044])).

fof(f129044,plain,
    ( spl9_130
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(sK1,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_130])])).

fof(f120776,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(sK1,sK1)),sK1)
    | ~ spl9_4
    | ~ spl9_118 ),
    inference(backward_demodulation,[],[f118008,f108])).

fof(f118008,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(sK3,sK1)),sK1)
    | ~ spl9_118 ),
    inference(resolution,[],[f117412,f26029])).

fof(f26029,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,X6)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X5),X6) ) ),
    inference(global_subsumption,[],[f123,f26026])).

fof(f26026,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,X6)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X5),X6)
      | r2_hidden(X5,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f26018])).

fof(f26018,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,X6)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X5),X6)
      | r2_hidden(X5,k1_xboole_0)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X5),X6) ) ),
    inference(superposition,[],[f71,f7348])).

fof(f7348,plain,(
    ! [X39,X38] :
      ( sK7(k1_tarski(X38),X39,k1_xboole_0) = X38
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X38),X39) ) ),
    inference(resolution,[],[f6834,f82])).

fof(f6834,plain,(
    ! [X52,X51] :
      ( r2_hidden(sK7(X51,X52,k1_xboole_0),X51)
      | k1_xboole_0 = k4_xboole_0(X51,X52) ) ),
    inference(resolution,[],[f70,f123])).

fof(f117412,plain,
    ( r2_hidden(sK6(sK3,sK1),sK1)
    | ~ spl9_118 ),
    inference(avatar_component_clause,[],[f117410])).

fof(f128610,plain,
    ( spl9_129
    | spl9_76 ),
    inference(avatar_split_clause,[],[f121966,f81297,f128607])).

fof(f81297,plain,
    ( spl9_76
  <=> r2_hidden(sK6(sK2,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_76])])).

fof(f121966,plain,
    ( sK2 = k4_xboole_0(sK2,k1_tarski(sK6(sK2,sK0)))
    | spl9_76 ),
    inference(resolution,[],[f81299,f111163])).

fof(f81299,plain,
    ( ~ r2_hidden(sK6(sK2,sK0),sK2)
    | spl9_76 ),
    inference(avatar_component_clause,[],[f81297])).

fof(f128605,plain,
    ( spl9_128
    | spl9_76 ),
    inference(avatar_split_clause,[],[f121952,f81297,f128602])).

fof(f128602,plain,
    ( spl9_128
  <=> k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(sK6(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_128])])).

fof(f121952,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(sK6(sK2,sK0)))
    | spl9_76 ),
    inference(resolution,[],[f81299,f1331])).

fof(f128301,plain,
    ( spl9_127
    | ~ spl9_77 ),
    inference(avatar_split_clause,[],[f81342,f81302,f128298])).

fof(f128298,plain,
    ( spl9_127
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(sK2,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_127])])).

fof(f81342,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(sK2,sK0)),sK0)
    | ~ spl9_77 ),
    inference(resolution,[],[f81304,f26029])).

fof(f127800,plain,
    ( spl9_126
    | ~ spl9_123 ),
    inference(avatar_split_clause,[],[f126562,f122817,f127797])).

fof(f127797,plain,
    ( spl9_126
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK0,k1_xboole_0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_126])])).

fof(f126562,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK0,k1_xboole_0)),sK2)
    | ~ spl9_123 ),
    inference(resolution,[],[f122819,f26029])).

fof(f127795,plain,
    ( spl9_125
    | spl9_122 ),
    inference(avatar_split_clause,[],[f126356,f122813,f127792])).

fof(f127792,plain,
    ( spl9_125
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK0,k1_xboole_0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_125])])).

fof(f122813,plain,
    ( spl9_122
  <=> r1_tarski(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_122])])).

fof(f126356,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK0,k1_xboole_0)),sK0)
    | spl9_122 ),
    inference(resolution,[],[f122814,f1637])).

fof(f1637,plain,(
    ! [X28,X27] :
      ( r1_tarski(X27,X28)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(X27,X28)),X27) ) ),
    inference(resolution,[],[f1304,f122])).

fof(f122814,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | spl9_122 ),
    inference(avatar_component_clause,[],[f122813])).

fof(f126950,plain,
    ( spl9_124
    | ~ spl9_73
    | ~ spl9_123 ),
    inference(avatar_split_clause,[],[f126902,f122817,f78248,f126947])).

fof(f126902,plain,
    ( r2_hidden(sK4(sK0,k1_xboole_0),sK0)
    | ~ spl9_73
    | ~ spl9_123 ),
    inference(resolution,[],[f80905,f122819])).

fof(f80905,plain,
    ( ! [X11] :
        ( ~ r2_hidden(X11,sK2)
        | r2_hidden(X11,sK0) )
    | ~ spl9_73 ),
    inference(superposition,[],[f90,f78250])).

fof(f126346,plain,
    ( spl9_1
    | ~ spl9_122 ),
    inference(avatar_split_clause,[],[f122823,f122813,f93])).

fof(f93,plain,
    ( spl9_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f122823,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_122 ),
    inference(forward_demodulation,[],[f122822,f126])).

fof(f122822,plain,
    ( sK0 = k3_xboole_0(sK0,k1_xboole_0)
    | ~ spl9_122 ),
    inference(resolution,[],[f122815,f54])).

fof(f122815,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl9_122 ),
    inference(avatar_component_clause,[],[f122813])).

fof(f122820,plain,
    ( spl9_122
    | spl9_123
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f121663,f5863,f122817,f122813])).

fof(f5863,plain,
    ( spl9_16
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f121663,plain,
    ( r2_hidden(sK4(sK0,k1_xboole_0),sK2)
    | r1_tarski(sK0,k1_xboole_0)
    | ~ spl9_16 ),
    inference(superposition,[],[f83321,f5865])).

fof(f5865,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f5863])).

fof(f121982,plain,
    ( spl9_121
    | ~ spl9_4
    | ~ spl9_117 ),
    inference(avatar_split_clause,[],[f120737,f117405,f107,f121979])).

fof(f117405,plain,
    ( spl9_117
  <=> r2_hidden(sK6(sK3,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_117])])).

fof(f120737,plain,
    ( r2_hidden(sK6(sK1,sK1),sK1)
    | ~ spl9_4
    | ~ spl9_117 ),
    inference(backward_demodulation,[],[f117406,f108])).

fof(f117406,plain,
    ( r2_hidden(sK6(sK3,sK1),sK3)
    | ~ spl9_117 ),
    inference(avatar_component_clause,[],[f117405])).

fof(f121507,plain,
    ( ~ spl9_120
    | ~ spl9_4
    | spl9_116 ),
    inference(avatar_split_clause,[],[f120736,f117398,f107,f121504])).

fof(f121504,plain,
    ( spl9_120
  <=> r2_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_120])])).

fof(f117398,plain,
    ( spl9_116
  <=> r2_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_116])])).

fof(f120736,plain,
    ( ~ r2_xboole_0(sK1,sK1)
    | ~ spl9_4
    | spl9_116 ),
    inference(backward_demodulation,[],[f117399,f108])).

fof(f117399,plain,
    ( ~ r2_xboole_0(sK3,sK1)
    | spl9_116 ),
    inference(avatar_component_clause,[],[f117398])).

fof(f118934,plain,(
    ~ spl9_119 ),
    inference(avatar_contradiction_clause,[],[f118921])).

fof(f118921,plain,
    ( $false
    | ~ spl9_119 ),
    inference(resolution,[],[f118919,f123])).

fof(f118919,plain,
    ( r2_hidden(sK6(sK3,sK1),k1_xboole_0)
    | ~ spl9_119 ),
    inference(avatar_component_clause,[],[f118917])).

fof(f118917,plain,
    ( spl9_119
  <=> r2_hidden(sK6(sK3,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_119])])).

fof(f118920,plain,
    ( spl9_119
    | ~ spl9_11
    | spl9_117
    | ~ spl9_118 ),
    inference(avatar_split_clause,[],[f118013,f117410,f117405,f3321,f118917])).

fof(f3321,plain,
    ( spl9_11
  <=> ! [X2] : k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(X2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f118013,plain,
    ( r2_hidden(sK6(sK3,sK1),k1_xboole_0)
    | ~ spl9_11
    | spl9_117
    | ~ spl9_118 ),
    inference(forward_demodulation,[],[f118005,f117971])).

fof(f117971,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK6(sK3,sK1)))
    | ~ spl9_11
    | spl9_117 ),
    inference(resolution,[],[f117407,f108879])).

fof(f108879,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK3)
        | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(X0)) )
    | ~ spl9_11 ),
    inference(condensation,[],[f108778])).

fof(f108778,plain,
    ( ! [X47,X48] :
        ( r2_hidden(X47,sK3)
        | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(X47))
        | k1_xboole_0 = k3_xboole_0(X48,k1_tarski(X47)) )
    | ~ spl9_11 ),
    inference(resolution,[],[f84580,f1331])).

fof(f84580,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,X5)
        | r2_hidden(X4,sK3)
        | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(X4)) )
    | ~ spl9_11 ),
    inference(backward_demodulation,[],[f46580,f84413])).

fof(f46580,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,k4_xboole_0(X5,k1_xboole_0))
        | r2_hidden(X4,sK3)
        | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(X4)) )
    | ~ spl9_11 ),
    inference(superposition,[],[f188,f46200])).

fof(f46200,plain,
    ( ! [X482] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X482),sK3)
        | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(X482)) )
    | ~ spl9_11 ),
    inference(superposition,[],[f3322,f41576])).

fof(f3322,plain,
    ( ! [X2] : k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(X2,sK3))
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f3321])).

fof(f117407,plain,
    ( ~ r2_hidden(sK6(sK3,sK1),sK3)
    | spl9_117 ),
    inference(avatar_component_clause,[],[f117405])).

fof(f118005,plain,
    ( r2_hidden(sK6(sK3,sK1),k3_xboole_0(sK1,k1_tarski(sK6(sK3,sK1))))
    | ~ spl9_118 ),
    inference(resolution,[],[f117412,f192])).

fof(f118016,plain,
    ( spl9_114
    | ~ spl9_115 ),
    inference(avatar_split_clause,[],[f117277,f117249,f116740])).

fof(f116740,plain,
    ( spl9_114
  <=> sK3 = k3_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_114])])).

fof(f117249,plain,
    ( spl9_115
  <=> sK3 = k3_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_115])])).

fof(f117277,plain,
    ( sK3 = k3_xboole_0(sK3,sK1)
    | ~ spl9_115 ),
    inference(superposition,[],[f273,f117251])).

fof(f117251,plain,
    ( sK3 = k3_xboole_0(sK1,sK3)
    | ~ spl9_115 ),
    inference(avatar_component_clause,[],[f117249])).

fof(f117828,plain,
    ( spl9_112
    | ~ spl9_115 ),
    inference(avatar_split_clause,[],[f117275,f117249,f116729])).

fof(f116729,plain,
    ( spl9_112
  <=> r1_tarski(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_112])])).

fof(f117275,plain,
    ( r1_tarski(sK3,sK1)
    | ~ spl9_115 ),
    inference(superposition,[],[f266,f117251])).

fof(f117441,plain,(
    ~ spl9_113 ),
    inference(avatar_contradiction_clause,[],[f117428])).

fof(f117428,plain,
    ( $false
    | ~ spl9_113 ),
    inference(resolution,[],[f116735,f123])).

fof(f116735,plain,
    ( r2_hidden(sK4(sK3,sK1),k1_xboole_0)
    | ~ spl9_113 ),
    inference(avatar_component_clause,[],[f116733])).

fof(f116733,plain,
    ( spl9_113
  <=> r2_hidden(sK4(sK3,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_113])])).

fof(f117426,plain,
    ( spl9_112
    | ~ spl9_115 ),
    inference(avatar_split_clause,[],[f117275,f117249,f116729])).

fof(f117413,plain,
    ( spl9_118
    | ~ spl9_116 ),
    inference(avatar_split_clause,[],[f117403,f117398,f117410])).

fof(f117403,plain,
    ( r2_hidden(sK6(sK3,sK1),sK1)
    | ~ spl9_116 ),
    inference(resolution,[],[f117400,f65])).

fof(f117400,plain,
    ( r2_xboole_0(sK3,sK1)
    | ~ spl9_116 ),
    inference(avatar_component_clause,[],[f117398])).

fof(f117408,plain,
    ( ~ spl9_117
    | ~ spl9_116 ),
    inference(avatar_split_clause,[],[f117402,f117398,f117405])).

fof(f117402,plain,
    ( ~ r2_hidden(sK6(sK3,sK1),sK3)
    | ~ spl9_116 ),
    inference(resolution,[],[f117400,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f117401,plain,
    ( spl9_116
    | spl9_4
    | ~ spl9_112 ),
    inference(avatar_split_clause,[],[f116737,f116729,f107,f117398])).

fof(f116737,plain,
    ( sK1 = sK3
    | r2_xboole_0(sK3,sK1)
    | ~ spl9_112 ),
    inference(resolution,[],[f116731,f55])).

fof(f116731,plain,
    ( r1_tarski(sK3,sK1)
    | ~ spl9_112 ),
    inference(avatar_component_clause,[],[f116729])).

fof(f117252,plain,
    ( spl9_115
    | ~ spl9_114 ),
    inference(avatar_split_clause,[],[f116744,f116740,f117249])).

fof(f116744,plain,
    ( sK3 = k3_xboole_0(sK1,sK3)
    | ~ spl9_114 ),
    inference(superposition,[],[f116742,f53])).

fof(f116742,plain,
    ( sK3 = k3_xboole_0(sK3,sK1)
    | ~ spl9_114 ),
    inference(avatar_component_clause,[],[f116740])).

fof(f116743,plain,
    ( spl9_114
    | ~ spl9_112 ),
    inference(avatar_split_clause,[],[f116738,f116729,f116740])).

fof(f116738,plain,
    ( sK3 = k3_xboole_0(sK3,sK1)
    | ~ spl9_112 ),
    inference(resolution,[],[f116731,f54])).

fof(f116736,plain,
    ( spl9_112
    | spl9_113
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f116725,f3921,f116733,f116729])).

fof(f3921,plain,
    ( spl9_13
  <=> k1_xboole_0 = k4_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f116725,plain,
    ( r2_hidden(sK4(sK3,sK1),k1_xboole_0)
    | r1_tarski(sK3,sK1)
    | ~ spl9_13 ),
    inference(duplicate_literal_removal,[],[f116710])).

fof(f116710,plain,
    ( r2_hidden(sK4(sK3,sK1),k1_xboole_0)
    | r1_tarski(sK3,sK1)
    | r1_tarski(sK3,sK1)
    | ~ spl9_13 ),
    inference(resolution,[],[f83312,f57])).

fof(f83312,plain,
    ( ! [X47] :
        ( r2_hidden(sK4(sK3,X47),sK1)
        | r2_hidden(sK4(sK3,X47),k1_xboole_0)
        | r1_tarski(sK3,X47) )
    | ~ spl9_13 ),
    inference(superposition,[],[f183,f3923])).

fof(f3923,plain,
    ( k1_xboole_0 = k4_xboole_0(sK3,sK1)
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f3921])).

fof(f116207,plain,
    ( ~ spl9_61
    | ~ spl9_36
    | spl9_59
    | ~ spl9_73 ),
    inference(avatar_split_clause,[],[f80318,f78248,f60577,f11051,f62743])).

fof(f62743,plain,
    ( spl9_61
  <=> r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_61])])).

fof(f11051,plain,
    ( spl9_36
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f60577,plain,
    ( spl9_59
  <=> r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_59])])).

fof(f80318,plain,
    ( ~ r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl9_36
    | spl9_59
    | ~ spl9_73 ),
    inference(backward_demodulation,[],[f60579,f79712])).

fof(f79712,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1)
    | ~ spl9_36
    | ~ spl9_73 ),
    inference(backward_demodulation,[],[f11053,f78250])).

fof(f11053,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)
    | ~ spl9_36 ),
    inference(avatar_component_clause,[],[f11051])).

fof(f60579,plain,
    ( ~ r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)),k2_zfmisc_1(sK0,sK1))
    | spl9_59 ),
    inference(avatar_component_clause,[],[f60577])).

fof(f105943,plain,
    ( spl9_111
    | ~ spl9_99 ),
    inference(avatar_split_clause,[],[f96687,f96677,f105940])).

fof(f105940,plain,
    ( spl9_111
  <=> r2_hidden(sK4(sK3,k1_xboole_0),k3_xboole_0(k3_xboole_0(sK1,sK3),k1_tarski(sK4(sK3,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_111])])).

fof(f96677,plain,
    ( spl9_99
  <=> r2_hidden(sK4(sK3,k1_xboole_0),k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_99])])).

fof(f96687,plain,
    ( r2_hidden(sK4(sK3,k1_xboole_0),k3_xboole_0(k3_xboole_0(sK1,sK3),k1_tarski(sK4(sK3,k1_xboole_0))))
    | ~ spl9_99 ),
    inference(resolution,[],[f96679,f192])).

fof(f96679,plain,
    ( r2_hidden(sK4(sK3,k1_xboole_0),k3_xboole_0(sK1,sK3))
    | ~ spl9_99 ),
    inference(avatar_component_clause,[],[f96677])).

fof(f102128,plain,
    ( spl9_110
    | ~ spl9_96 ),
    inference(avatar_split_clause,[],[f96464,f96454,f102125])).

fof(f102125,plain,
    ( spl9_110
  <=> r2_hidden(sK4(sK1,k1_xboole_0),k3_xboole_0(k3_xboole_0(sK1,sK3),k1_tarski(sK4(sK1,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_110])])).

fof(f96454,plain,
    ( spl9_96
  <=> r2_hidden(sK4(sK1,k1_xboole_0),k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_96])])).

fof(f96464,plain,
    ( r2_hidden(sK4(sK1,k1_xboole_0),k3_xboole_0(k3_xboole_0(sK1,sK3),k1_tarski(sK4(sK1,k1_xboole_0))))
    | ~ spl9_96 ),
    inference(resolution,[],[f96456,f192])).

fof(f96456,plain,
    ( r2_hidden(sK4(sK1,k1_xboole_0),k3_xboole_0(sK1,sK3))
    | ~ spl9_96 ),
    inference(avatar_component_clause,[],[f96454])).

fof(f98586,plain,
    ( spl9_109
    | ~ spl9_100 ),
    inference(avatar_split_clause,[],[f96701,f96693,f98583])).

fof(f98583,plain,
    ( spl9_109
  <=> r2_hidden(sK4(sK3,k1_xboole_0),k3_xboole_0(sK3,k1_tarski(sK4(sK3,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_109])])).

fof(f96693,plain,
    ( spl9_100
  <=> r2_hidden(sK4(sK3,k1_xboole_0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_100])])).

fof(f96701,plain,
    ( r2_hidden(sK4(sK3,k1_xboole_0),k3_xboole_0(sK3,k1_tarski(sK4(sK3,k1_xboole_0))))
    | ~ spl9_100 ),
    inference(resolution,[],[f96695,f192])).

fof(f96695,plain,
    ( r2_hidden(sK4(sK3,k1_xboole_0),sK3)
    | ~ spl9_100 ),
    inference(avatar_component_clause,[],[f96693])).

fof(f98581,plain,
    ( spl9_97
    | spl9_108
    | ~ spl9_94 ),
    inference(avatar_split_clause,[],[f95177,f95091,f98579,f96470])).

fof(f98579,plain,
    ( spl9_108
  <=> ! [X1] : ~ r2_hidden(sK4(sK1,k1_xboole_0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_108])])).

fof(f95091,plain,
    ( spl9_94
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK1,k1_xboole_0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_94])])).

fof(f95177,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK4(sK1,k1_xboole_0),X1)
        | r2_hidden(sK4(sK1,k1_xboole_0),sK1) )
    | ~ spl9_94 ),
    inference(forward_demodulation,[],[f95103,f84413])).

fof(f95103,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK4(sK1,k1_xboole_0),k4_xboole_0(X1,k1_xboole_0))
        | r2_hidden(sK4(sK1,k1_xboole_0),sK1) )
    | ~ spl9_94 ),
    inference(superposition,[],[f188,f95093])).

fof(f95093,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK1,k1_xboole_0)),sK1)
    | ~ spl9_94 ),
    inference(avatar_component_clause,[],[f95091])).

fof(f98577,plain,
    ( spl9_97
    | spl9_107
    | ~ spl9_94 ),
    inference(avatar_split_clause,[],[f95101,f95091,f98574,f96470])).

fof(f98574,plain,
    ( spl9_107
  <=> r2_hidden(sK4(sK1,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_107])])).

fof(f95101,plain,
    ( r2_hidden(sK4(sK1,k1_xboole_0),k1_xboole_0)
    | r2_hidden(sK4(sK1,k1_xboole_0),sK1)
    | ~ spl9_94 ),
    inference(superposition,[],[f182,f95093])).

fof(f98060,plain,
    ( spl9_106
    | ~ spl9_99 ),
    inference(avatar_split_clause,[],[f96690,f96677,f98057])).

fof(f98057,plain,
    ( spl9_106
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK3,k1_xboole_0)),k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_106])])).

fof(f96690,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK3,k1_xboole_0)),k3_xboole_0(sK1,sK3))
    | ~ spl9_99 ),
    inference(resolution,[],[f96679,f26029])).

fof(f98055,plain,
    ( spl9_100
    | spl9_105
    | ~ spl9_92 ),
    inference(avatar_split_clause,[],[f94976,f94890,f98053,f96693])).

fof(f98053,plain,
    ( spl9_105
  <=> ! [X1] : ~ r2_hidden(sK4(sK3,k1_xboole_0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_105])])).

fof(f94890,plain,
    ( spl9_92
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK3,k1_xboole_0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_92])])).

fof(f94976,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK4(sK3,k1_xboole_0),X1)
        | r2_hidden(sK4(sK3,k1_xboole_0),sK3) )
    | ~ spl9_92 ),
    inference(forward_demodulation,[],[f94902,f84413])).

fof(f94902,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK4(sK3,k1_xboole_0),k4_xboole_0(X1,k1_xboole_0))
        | r2_hidden(sK4(sK3,k1_xboole_0),sK3) )
    | ~ spl9_92 ),
    inference(superposition,[],[f188,f94892])).

fof(f94892,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK3,k1_xboole_0)),sK3)
    | ~ spl9_92 ),
    inference(avatar_component_clause,[],[f94890])).

fof(f98051,plain,
    ( spl9_100
    | spl9_104
    | ~ spl9_92 ),
    inference(avatar_split_clause,[],[f94900,f94890,f98048,f96693])).

fof(f98048,plain,
    ( spl9_104
  <=> r2_hidden(sK4(sK3,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_104])])).

fof(f94900,plain,
    ( r2_hidden(sK4(sK3,k1_xboole_0),k1_xboole_0)
    | r2_hidden(sK4(sK3,k1_xboole_0),sK3)
    | ~ spl9_92 ),
    inference(superposition,[],[f182,f94892])).

fof(f98046,plain,
    ( spl9_103
    | ~ spl9_91 ),
    inference(avatar_split_clause,[],[f94150,f90285,f98043])).

fof(f98043,plain,
    ( spl9_103
  <=> r2_hidden(sK4(sK1,k1_xboole_0),k3_xboole_0(sK3,k1_tarski(sK4(sK1,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_103])])).

fof(f90285,plain,
    ( spl9_91
  <=> r2_hidden(sK4(sK1,k1_xboole_0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_91])])).

fof(f94150,plain,
    ( r2_hidden(sK4(sK1,k1_xboole_0),k3_xboole_0(sK3,k1_tarski(sK4(sK1,k1_xboole_0))))
    | ~ spl9_91 ),
    inference(resolution,[],[f90287,f192])).

fof(f90287,plain,
    ( r2_hidden(sK4(sK1,k1_xboole_0),sK3)
    | ~ spl9_91 ),
    inference(avatar_component_clause,[],[f90285])).

fof(f97209,plain,
    ( spl9_102
    | ~ spl9_97 ),
    inference(avatar_split_clause,[],[f96478,f96470,f97206])).

fof(f97206,plain,
    ( spl9_102
  <=> r2_hidden(sK4(sK1,k1_xboole_0),k3_xboole_0(sK1,k1_tarski(sK4(sK1,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_102])])).

fof(f96478,plain,
    ( r2_hidden(sK4(sK1,k1_xboole_0),k3_xboole_0(sK1,k1_tarski(sK4(sK1,k1_xboole_0))))
    | ~ spl9_97 ),
    inference(resolution,[],[f96472,f192])).

fof(f97204,plain,
    ( spl9_101
    | ~ spl9_89 ),
    inference(avatar_split_clause,[],[f89585,f85170,f97201])).

fof(f97201,plain,
    ( spl9_101
  <=> r2_hidden(sK4(sK3,k1_xboole_0),k3_xboole_0(sK1,k1_tarski(sK4(sK3,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_101])])).

fof(f85170,plain,
    ( spl9_89
  <=> r2_hidden(sK4(sK3,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_89])])).

fof(f89585,plain,
    ( r2_hidden(sK4(sK3,k1_xboole_0),k3_xboole_0(sK1,k1_tarski(sK4(sK3,k1_xboole_0))))
    | ~ spl9_89 ),
    inference(resolution,[],[f85172,f192])).

fof(f85172,plain,
    ( r2_hidden(sK4(sK3,k1_xboole_0),sK1)
    | ~ spl9_89 ),
    inference(avatar_component_clause,[],[f85170])).

fof(f96696,plain,
    ( spl9_100
    | ~ spl9_99 ),
    inference(avatar_split_clause,[],[f96682,f96677,f96693])).

fof(f96682,plain,
    ( r2_hidden(sK4(sK3,k1_xboole_0),sK3)
    | ~ spl9_99 ),
    inference(resolution,[],[f96679,f89])).

fof(f96680,plain,
    ( spl9_88
    | spl9_99
    | ~ spl9_43 ),
    inference(avatar_split_clause,[],[f84337,f13386,f96677,f85166])).

fof(f85166,plain,
    ( spl9_88
  <=> r1_tarski(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_88])])).

fof(f13386,plain,
    ( spl9_43
  <=> k1_xboole_0 = k4_xboole_0(sK3,k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).

fof(f84337,plain,
    ( r2_hidden(sK4(sK3,k1_xboole_0),k3_xboole_0(sK1,sK3))
    | r1_tarski(sK3,k1_xboole_0)
    | ~ spl9_43 ),
    inference(superposition,[],[f83321,f13388])).

fof(f13388,plain,
    ( k1_xboole_0 = k4_xboole_0(sK3,k3_xboole_0(sK1,sK3))
    | ~ spl9_43 ),
    inference(avatar_component_clause,[],[f13386])).

fof(f96580,plain,
    ( spl9_98
    | ~ spl9_96 ),
    inference(avatar_split_clause,[],[f96467,f96454,f96577])).

fof(f96577,plain,
    ( spl9_98
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK1,k1_xboole_0)),k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_98])])).

fof(f96467,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK1,k1_xboole_0)),k3_xboole_0(sK1,sK3))
    | ~ spl9_96 ),
    inference(resolution,[],[f96456,f26029])).

fof(f96473,plain,
    ( spl9_97
    | ~ spl9_96 ),
    inference(avatar_split_clause,[],[f96458,f96454,f96470])).

fof(f96458,plain,
    ( r2_hidden(sK4(sK1,k1_xboole_0),sK1)
    | ~ spl9_96 ),
    inference(resolution,[],[f96456,f90])).

fof(f96457,plain,
    ( spl9_90
    | spl9_96
    | ~ spl9_31 ),
    inference(avatar_split_clause,[],[f84336,f9089,f96454,f90281])).

fof(f90281,plain,
    ( spl9_90
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_90])])).

fof(f9089,plain,
    ( spl9_31
  <=> k1_xboole_0 = k4_xboole_0(sK1,k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f84336,plain,
    ( r2_hidden(sK4(sK1,k1_xboole_0),k3_xboole_0(sK1,sK3))
    | r1_tarski(sK1,k1_xboole_0)
    | ~ spl9_31 ),
    inference(superposition,[],[f83321,f9091])).

fof(f9091,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k3_xboole_0(sK1,sK3))
    | ~ spl9_31 ),
    inference(avatar_component_clause,[],[f9089])).

fof(f95099,plain,
    ( spl9_95
    | ~ spl9_91 ),
    inference(avatar_split_clause,[],[f94153,f90285,f95096])).

fof(f95096,plain,
    ( spl9_95
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK1,k1_xboole_0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_95])])).

fof(f94153,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK1,k1_xboole_0)),sK3)
    | ~ spl9_91 ),
    inference(resolution,[],[f90287,f26029])).

fof(f95094,plain,
    ( spl9_94
    | spl9_90 ),
    inference(avatar_split_clause,[],[f93964,f90281,f95091])).

fof(f93964,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK1,k1_xboole_0)),sK1)
    | spl9_90 ),
    inference(resolution,[],[f90282,f1637])).

fof(f90282,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | spl9_90 ),
    inference(avatar_component_clause,[],[f90281])).

fof(f94898,plain,
    ( spl9_93
    | ~ spl9_89 ),
    inference(avatar_split_clause,[],[f89588,f85170,f94895])).

fof(f94895,plain,
    ( spl9_93
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK3,k1_xboole_0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_93])])).

fof(f89588,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK3,k1_xboole_0)),sK1)
    | ~ spl9_89 ),
    inference(resolution,[],[f85172,f26029])).

fof(f94893,plain,
    ( spl9_92
    | spl9_88 ),
    inference(avatar_split_clause,[],[f89408,f85166,f94890])).

fof(f89408,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK3,k1_xboole_0)),sK3)
    | spl9_88 ),
    inference(resolution,[],[f85167,f1637])).

fof(f85167,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | spl9_88 ),
    inference(avatar_component_clause,[],[f85166])).

fof(f93954,plain,
    ( spl9_2
    | ~ spl9_90 ),
    inference(avatar_split_clause,[],[f90291,f90281,f98])).

fof(f90291,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_90 ),
    inference(forward_demodulation,[],[f90290,f126])).

fof(f90290,plain,
    ( sK1 = k3_xboole_0(sK1,k1_xboole_0)
    | ~ spl9_90 ),
    inference(resolution,[],[f90283,f54])).

fof(f90283,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl9_90 ),
    inference(avatar_component_clause,[],[f90281])).

fof(f90288,plain,
    ( spl9_90
    | spl9_91
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f84346,f3268,f90285,f90281])).

fof(f3268,plain,
    ( spl9_10
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f84346,plain,
    ( r2_hidden(sK4(sK1,k1_xboole_0),sK3)
    | r1_tarski(sK1,k1_xboole_0)
    | ~ spl9_10 ),
    inference(superposition,[],[f83321,f3270])).

fof(f3270,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK3)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f3268])).

fof(f89398,plain,
    ( spl9_6
    | ~ spl9_88 ),
    inference(avatar_split_clause,[],[f85176,f85166,f170])).

fof(f170,plain,
    ( spl9_6
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f85176,plain,
    ( k1_xboole_0 = sK3
    | ~ spl9_88 ),
    inference(forward_demodulation,[],[f85175,f126])).

fof(f85175,plain,
    ( sK3 = k3_xboole_0(sK3,k1_xboole_0)
    | ~ spl9_88 ),
    inference(resolution,[],[f85168,f54])).

fof(f85168,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl9_88 ),
    inference(avatar_component_clause,[],[f85166])).

fof(f85173,plain,
    ( spl9_88
    | spl9_89
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f84344,f3921,f85170,f85166])).

fof(f84344,plain,
    ( r2_hidden(sK4(sK3,k1_xboole_0),sK1)
    | r1_tarski(sK3,k1_xboole_0)
    | ~ spl9_13 ),
    inference(superposition,[],[f83321,f3923])).

fof(f83349,plain,
    ( spl9_87
    | ~ spl9_3
    | ~ spl9_77 ),
    inference(avatar_split_clause,[],[f82639,f81302,f103,f83346])).

fof(f83346,plain,
    ( spl9_87
  <=> r2_hidden(sK6(sK0,sK0),k3_xboole_0(sK0,k1_tarski(sK6(sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_87])])).

fof(f103,plain,
    ( spl9_3
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f82639,plain,
    ( r2_hidden(sK6(sK0,sK0),k3_xboole_0(sK0,k1_tarski(sK6(sK0,sK0))))
    | ~ spl9_3
    | ~ spl9_77 ),
    inference(backward_demodulation,[],[f81338,f104])).

fof(f104,plain,
    ( sK0 = sK2
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f81338,plain,
    ( r2_hidden(sK6(sK2,sK0),k3_xboole_0(sK0,k1_tarski(sK6(sK2,sK0))))
    | ~ spl9_77 ),
    inference(resolution,[],[f81304,f192])).

fof(f83327,plain,
    ( spl9_86
    | ~ spl9_3
    | ~ spl9_78 ),
    inference(avatar_split_clause,[],[f82689,f81578,f103,f83324])).

fof(f83324,plain,
    ( spl9_86
  <=> r2_hidden(sK6(k1_xboole_0,sK0),k3_xboole_0(sK0,k1_tarski(sK6(k1_xboole_0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_86])])).

fof(f82689,plain,
    ( r2_hidden(sK6(k1_xboole_0,sK0),k3_xboole_0(sK0,k1_tarski(sK6(k1_xboole_0,sK0))))
    | ~ spl9_3
    | ~ spl9_78 ),
    inference(backward_demodulation,[],[f81586,f104])).

fof(f81586,plain,
    ( r2_hidden(sK6(k1_xboole_0,sK2),k3_xboole_0(sK0,k1_tarski(sK6(k1_xboole_0,sK2))))
    | ~ spl9_78 ),
    inference(resolution,[],[f81580,f192])).

fof(f83168,plain,
    ( spl9_85
    | ~ spl9_3
    | ~ spl9_77 ),
    inference(avatar_split_clause,[],[f82642,f81302,f103,f83165])).

fof(f83165,plain,
    ( spl9_85
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(sK0,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_85])])).

fof(f82642,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(sK0,sK0)),sK0)
    | ~ spl9_3
    | ~ spl9_77 ),
    inference(backward_demodulation,[],[f81342,f104])).

fof(f83073,plain,
    ( spl9_84
    | ~ spl9_3
    | ~ spl9_79 ),
    inference(avatar_split_clause,[],[f82721,f81640,f103,f83070])).

fof(f83070,plain,
    ( spl9_84
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k1_xboole_0,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_84])])).

fof(f81640,plain,
    ( spl9_79
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k1_xboole_0,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_79])])).

fof(f82721,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k1_xboole_0,sK0)),sK0)
    | ~ spl9_3
    | ~ spl9_79 ),
    inference(backward_demodulation,[],[f81642,f104])).

fof(f81642,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k1_xboole_0,sK2)),sK0)
    | ~ spl9_79 ),
    inference(avatar_component_clause,[],[f81640])).

fof(f82972,plain,
    ( spl9_83
    | ~ spl9_3
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f82633,f81297,f103,f82969])).

fof(f82969,plain,
    ( spl9_83
  <=> r2_hidden(sK6(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_83])])).

fof(f82633,plain,
    ( r2_hidden(sK6(sK0,sK0),sK0)
    | ~ spl9_3
    | ~ spl9_76 ),
    inference(backward_demodulation,[],[f81298,f104])).

fof(f81298,plain,
    ( r2_hidden(sK6(sK2,sK0),sK2)
    | ~ spl9_76 ),
    inference(avatar_component_clause,[],[f81297])).

fof(f82957,plain,
    ( spl9_82
    | ~ spl9_3
    | ~ spl9_78 ),
    inference(avatar_split_clause,[],[f82684,f81578,f103,f82954])).

fof(f82954,plain,
    ( spl9_82
  <=> r2_hidden(sK6(k1_xboole_0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_82])])).

fof(f82684,plain,
    ( r2_hidden(sK6(k1_xboole_0,sK0),sK0)
    | ~ spl9_3
    | ~ spl9_78 ),
    inference(backward_demodulation,[],[f81580,f104])).

fof(f82952,plain,
    ( ~ spl9_81
    | ~ spl9_3
    | spl9_75 ),
    inference(avatar_split_clause,[],[f82632,f81290,f103,f82949])).

fof(f82949,plain,
    ( spl9_81
  <=> r2_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_81])])).

fof(f81290,plain,
    ( spl9_75
  <=> r2_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_75])])).

fof(f82632,plain,
    ( ~ r2_xboole_0(sK0,sK0)
    | ~ spl9_3
    | spl9_75 ),
    inference(backward_demodulation,[],[f81291,f104])).

fof(f81291,plain,
    ( ~ r2_xboole_0(sK2,sK0)
    | spl9_75 ),
    inference(avatar_component_clause,[],[f81290])).

fof(f81748,plain,
    ( spl9_80
    | spl9_76 ),
    inference(avatar_split_clause,[],[f81307,f81297,f81745])).

fof(f81745,plain,
    ( spl9_80
  <=> k1_xboole_0 = k3_xboole_0(k1_tarski(sK6(sK2,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_80])])).

fof(f81307,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_tarski(sK6(sK2,sK0)),sK2)
    | spl9_76 ),
    inference(resolution,[],[f81299,f963])).

fof(f81643,plain,
    ( spl9_79
    | ~ spl9_78 ),
    inference(avatar_split_clause,[],[f81590,f81578,f81640])).

fof(f81590,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k1_xboole_0,sK2)),sK0)
    | ~ spl9_78 ),
    inference(resolution,[],[f81580,f26029])).

fof(f81638,plain,
    ( spl9_3
    | spl9_77
    | ~ spl9_73 ),
    inference(avatar_split_clause,[],[f80922,f78248,f81302,f103])).

fof(f80922,plain,
    ( r2_hidden(sK6(sK2,sK0),sK0)
    | sK0 = sK2
    | ~ spl9_73 ),
    inference(superposition,[],[f375,f78250])).

fof(f375,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK6(k3_xboole_0(X2,X3),X2),X2)
      | k3_xboole_0(X2,X3) = X2 ) ),
    inference(resolution,[],[f272,f65])).

fof(f272,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(k3_xboole_0(X0,X1),X0)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(resolution,[],[f266,f55])).

fof(f81637,plain,
    ( spl9_3
    | ~ spl9_76
    | ~ spl9_73 ),
    inference(avatar_split_clause,[],[f80921,f78248,f81297,f103])).

fof(f80921,plain,
    ( ~ r2_hidden(sK6(sK2,sK0),sK2)
    | sK0 = sK2
    | ~ spl9_73 ),
    inference(superposition,[],[f374,f78250])).

fof(f374,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(k3_xboole_0(X0,X1),X0),k3_xboole_0(X0,X1))
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(resolution,[],[f272,f66])).

fof(f81581,plain,
    ( spl9_7
    | spl9_78
    | ~ spl9_73 ),
    inference(avatar_split_clause,[],[f80908,f78248,f81578,f174])).

fof(f80908,plain,
    ( r2_hidden(sK6(k1_xboole_0,sK2),sK0)
    | k1_xboole_0 = sK2
    | ~ spl9_73 ),
    inference(superposition,[],[f153,f78250])).

fof(f81458,plain,
    ( spl9_58
    | ~ spl9_36
    | ~ spl9_73 ),
    inference(avatar_split_clause,[],[f79712,f78248,f11051,f60570])).

fof(f60570,plain,
    ( spl9_58
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_58])])).

fof(f81305,plain,
    ( spl9_77
    | ~ spl9_75 ),
    inference(avatar_split_clause,[],[f81295,f81290,f81302])).

fof(f81295,plain,
    ( r2_hidden(sK6(sK2,sK0),sK0)
    | ~ spl9_75 ),
    inference(resolution,[],[f81292,f65])).

fof(f81292,plain,
    ( r2_xboole_0(sK2,sK0)
    | ~ spl9_75 ),
    inference(avatar_component_clause,[],[f81290])).

fof(f81300,plain,
    ( ~ spl9_76
    | ~ spl9_75 ),
    inference(avatar_split_clause,[],[f81294,f81290,f81297])).

fof(f81294,plain,
    ( ~ r2_hidden(sK6(sK2,sK0),sK2)
    | ~ spl9_75 ),
    inference(resolution,[],[f81292,f66])).

fof(f81293,plain,
    ( spl9_3
    | spl9_75
    | ~ spl9_73 ),
    inference(avatar_split_clause,[],[f80915,f78248,f81290,f103])).

fof(f80915,plain,
    ( r2_xboole_0(sK2,sK0)
    | sK0 = sK2
    | ~ spl9_73 ),
    inference(superposition,[],[f272,f78250])).

fof(f81066,plain,
    ( spl9_74
    | ~ spl9_73 ),
    inference(avatar_split_clause,[],[f80916,f78248,f78255])).

fof(f78255,plain,
    ( spl9_74
  <=> sK2 = k3_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_74])])).

fof(f80916,plain,
    ( sK2 = k3_xboole_0(sK2,sK0)
    | ~ spl9_73 ),
    inference(superposition,[],[f273,f78250])).

fof(f81063,plain,
    ( spl9_71
    | ~ spl9_74 ),
    inference(avatar_split_clause,[],[f78296,f78255,f78240])).

fof(f78240,plain,
    ( spl9_71
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_71])])).

fof(f78296,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl9_74 ),
    inference(superposition,[],[f261,f78257])).

fof(f78257,plain,
    ( sK2 = k3_xboole_0(sK2,sK0)
    | ~ spl9_74 ),
    inference(avatar_component_clause,[],[f78255])).

fof(f81049,plain,
    ( spl9_71
    | ~ spl9_73 ),
    inference(avatar_split_clause,[],[f80914,f78248,f78240])).

fof(f80914,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl9_73 ),
    inference(superposition,[],[f266,f78250])).

fof(f79678,plain,(
    ~ spl9_72 ),
    inference(avatar_contradiction_clause,[],[f79668])).

fof(f79668,plain,
    ( $false
    | ~ spl9_72 ),
    inference(resolution,[],[f78246,f123])).

fof(f78246,plain,
    ( r2_hidden(sK4(sK2,sK0),k1_xboole_0)
    | ~ spl9_72 ),
    inference(avatar_component_clause,[],[f78244])).

fof(f78244,plain,
    ( spl9_72
  <=> r2_hidden(sK4(sK2,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_72])])).

fof(f79656,plain,
    ( spl9_73
    | ~ spl9_74 ),
    inference(avatar_split_clause,[],[f78259,f78255,f78248])).

fof(f78259,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | ~ spl9_74 ),
    inference(superposition,[],[f78257,f53])).

fof(f78258,plain,
    ( spl9_74
    | ~ spl9_71 ),
    inference(avatar_split_clause,[],[f78253,f78240,f78255])).

fof(f78253,plain,
    ( sK2 = k3_xboole_0(sK2,sK0)
    | ~ spl9_71 ),
    inference(resolution,[],[f78242,f54])).

fof(f78242,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl9_71 ),
    inference(avatar_component_clause,[],[f78240])).

fof(f78251,plain,
    ( spl9_71
    | spl9_72
    | spl9_73
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f78033,f6922,f78248,f78244,f78240])).

fof(f6922,plain,
    ( spl9_22
  <=> ! [X14] : k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X14,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f78033,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | r2_hidden(sK4(sK2,sK0),k1_xboole_0)
    | r1_tarski(sK2,sK0)
    | ~ spl9_22 ),
    inference(forward_demodulation,[],[f77939,f53])).

fof(f77939,plain,
    ( r2_hidden(sK4(sK2,sK0),k1_xboole_0)
    | r1_tarski(sK2,sK0)
    | sK2 = k3_xboole_0(sK2,sK0)
    | ~ spl9_22 ),
    inference(superposition,[],[f198,f77912])).

fof(f77912,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(sK4(X1,sK0)))
        | k3_xboole_0(X1,sK0) = X1 )
    | ~ spl9_22 ),
    inference(resolution,[],[f77819,f54])).

fof(f77819,plain,
    ( ! [X13] :
        ( r1_tarski(X13,sK0)
        | k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(sK4(X13,sK0))) )
    | ~ spl9_22 ),
    inference(resolution,[],[f77725,f57])).

fof(f77725,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK0)
        | k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(X0)) )
    | ~ spl9_22 ),
    inference(resolution,[],[f46279,f2026])).

fof(f46279,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,k4_xboole_0(X5,k1_xboole_0))
        | r2_hidden(X4,sK0)
        | k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(X4)) )
    | ~ spl9_22 ),
    inference(superposition,[],[f188,f46187])).

fof(f46187,plain,
    ( ! [X451] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X451),sK0)
        | k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(X451)) )
    | ~ spl9_22 ),
    inference(superposition,[],[f6923,f41576])).

fof(f6923,plain,
    ( ! [X14] : k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X14,sK0))
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f6922])).

fof(f198,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK4(X3,X4),k3_xboole_0(X3,k1_tarski(sK4(X3,X4))))
      | r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f192,f56])).

fof(f77183,plain,
    ( spl9_70
    | ~ spl9_65 ),
    inference(avatar_split_clause,[],[f69727,f69715,f77180])).

fof(f77180,plain,
    ( spl9_70
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))),k2_zfmisc_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_70])])).

fof(f69715,plain,
    ( spl9_65
  <=> r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_65])])).

fof(f69727,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))),k2_zfmisc_1(sK2,sK1))
    | ~ spl9_65 ),
    inference(resolution,[],[f69717,f26029])).

fof(f69717,plain,
    ( r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK2,sK1))
    | ~ spl9_65 ),
    inference(avatar_component_clause,[],[f69715])).

fof(f76279,plain,
    ( spl9_69
    | ~ spl9_60 ),
    inference(avatar_split_clause,[],[f69435,f60582,f76276])).

fof(f76276,plain,
    ( spl9_69
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))),k2_zfmisc_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_69])])).

fof(f60582,plain,
    ( spl9_60
  <=> r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)),k2_zfmisc_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_60])])).

fof(f69435,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))),k2_zfmisc_1(sK2,sK1))
    | ~ spl9_60 ),
    inference(resolution,[],[f60584,f26029])).

fof(f60584,plain,
    ( r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)),k2_zfmisc_1(sK2,sK1))
    | ~ spl9_60 ),
    inference(avatar_component_clause,[],[f60582])).

fof(f76274,plain,
    ( spl9_68
    | spl9_59 ),
    inference(avatar_split_clause,[],[f69413,f60577,f76271])).

fof(f76271,plain,
    ( spl9_68
  <=> k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k1_tarski(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_68])])).

fof(f69413,plain,
    ( k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k1_tarski(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))))
    | spl9_59 ),
    inference(resolution,[],[f60579,f1331])).

fof(f76269,plain,
    ( spl9_67
    | spl9_59 ),
    inference(avatar_split_clause,[],[f69400,f60577,f76266])).

fof(f76266,plain,
    ( spl9_67
  <=> k1_xboole_0 = k3_xboole_0(k1_tarski(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_67])])).

fof(f69400,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_tarski(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))),k2_zfmisc_1(sK0,sK1))
    | spl9_59 ),
    inference(resolution,[],[f60579,f963])).

fof(f75656,plain,
    ( spl9_8
    | spl9_63
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f11038,f10903,f67300,f178])).

fof(f178,plain,
    ( spl9_8
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f67300,plain,
    ( spl9_63
  <=> r2_hidden(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_63])])).

fof(f10903,plain,
    ( spl9_34
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f11038,plain,
    ( r2_hidden(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK2,sK1))
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl9_34 ),
    inference(resolution,[],[f10933,f151])).

fof(f10933,plain,
    ( ! [X20] :
        ( ~ r2_hidden(X20,k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X20,k2_zfmisc_1(sK2,sK1)) )
    | ~ spl9_34 ),
    inference(superposition,[],[f2967,f10905])).

fof(f10905,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))
    | ~ spl9_34 ),
    inference(avatar_component_clause,[],[f10903])).

fof(f2967,plain,(
    ! [X30,X33,X31,X32] :
      ( ~ r2_hidden(X33,k2_zfmisc_1(X30,k3_xboole_0(X31,X32)))
      | r2_hidden(X33,k2_zfmisc_1(X30,X31)) ) ),
    inference(superposition,[],[f90,f2034])).

fof(f2034,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f79,f52])).

fof(f52,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f79,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f70369,plain,
    ( spl9_66
    | ~ spl9_49
    | ~ spl9_53 ),
    inference(avatar_split_clause,[],[f55866,f53031,f52876,f70366])).

fof(f70366,plain,
    ( spl9_66
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_66])])).

fof(f52876,plain,
    ( spl9_49
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).

fof(f53031,plain,
    ( spl9_53
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),k2_zfmisc_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_53])])).

fof(f55866,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),k2_zfmisc_1(sK0,sK1))
    | ~ spl9_49
    | ~ spl9_53 ),
    inference(backward_demodulation,[],[f53033,f52878])).

fof(f52878,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3)
    | ~ spl9_49 ),
    inference(avatar_component_clause,[],[f52876])).

fof(f53033,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),k2_zfmisc_1(sK0,sK3))
    | ~ spl9_53 ),
    inference(avatar_component_clause,[],[f53031])).

fof(f69718,plain,
    ( spl9_65
    | ~ spl9_34
    | ~ spl9_61 ),
    inference(avatar_split_clause,[],[f69555,f62743,f10903,f69715])).

fof(f69555,plain,
    ( r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK2,sK1))
    | ~ spl9_34
    | ~ spl9_61 ),
    inference(resolution,[],[f62744,f10933])).

fof(f62744,plain,
    ( r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl9_61 ),
    inference(avatar_component_clause,[],[f62743])).

fof(f69624,plain,
    ( spl9_64
    | ~ spl9_63 ),
    inference(avatar_split_clause,[],[f67312,f67300,f69621])).

fof(f69621,plain,
    ( spl9_64
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),k2_zfmisc_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_64])])).

fof(f67312,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),k2_zfmisc_1(sK2,sK1))
    | ~ spl9_63 ),
    inference(resolution,[],[f67302,f26029])).

fof(f67302,plain,
    ( r2_hidden(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK2,sK1))
    | ~ spl9_63 ),
    inference(avatar_component_clause,[],[f67300])).

fof(f69554,plain,
    ( spl9_61
    | ~ spl9_49
    | ~ spl9_50 ),
    inference(avatar_split_clause,[],[f66741,f52883,f52876,f62743])).

fof(f52883,plain,
    ( spl9_50
  <=> r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).

fof(f66741,plain,
    ( r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl9_49
    | ~ spl9_50 ),
    inference(backward_demodulation,[],[f52884,f52878])).

fof(f52884,plain,
    ( r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK0,sK1))
    | ~ spl9_50 ),
    inference(avatar_component_clause,[],[f52883])).

fof(f67303,plain,
    ( spl9_63
    | ~ spl9_34
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f67263,f56540,f10903,f67300])).

fof(f56540,plain,
    ( spl9_56
  <=> r2_hidden(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).

fof(f67263,plain,
    ( r2_hidden(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK2,sK1))
    | ~ spl9_34
    | ~ spl9_56 ),
    inference(resolution,[],[f10933,f56542])).

fof(f56542,plain,
    ( r2_hidden(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl9_56 ),
    inference(avatar_component_clause,[],[f56540])).

fof(f66307,plain,
    ( spl9_62
    | spl9_50 ),
    inference(avatar_split_clause,[],[f52892,f52883,f66304])).

fof(f66304,plain,
    ( spl9_62
  <=> k1_xboole_0 = k3_xboole_0(k1_tarski(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).

fof(f52892,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_tarski(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))),k2_zfmisc_1(sK0,sK1))
    | spl9_50 ),
    inference(resolution,[],[f52885,f963])).

fof(f52885,plain,
    ( ~ r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK0,sK1))
    | spl9_50 ),
    inference(avatar_component_clause,[],[f52883])).

fof(f62746,plain,
    ( ~ spl9_61
    | ~ spl9_58
    | spl9_59 ),
    inference(avatar_split_clause,[],[f60967,f60577,f60570,f62743])).

fof(f60967,plain,
    ( ~ r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl9_58
    | spl9_59 ),
    inference(backward_demodulation,[],[f60579,f60572])).

fof(f60572,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1)
    | ~ spl9_58 ),
    inference(avatar_component_clause,[],[f60570])).

fof(f60585,plain,
    ( spl9_60
    | ~ spl9_57 ),
    inference(avatar_split_clause,[],[f60575,f60566,f60582])).

fof(f60566,plain,
    ( spl9_57
  <=> r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_57])])).

fof(f60575,plain,
    ( r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)),k2_zfmisc_1(sK2,sK1))
    | ~ spl9_57 ),
    inference(resolution,[],[f60568,f65])).

fof(f60568,plain,
    ( r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))
    | ~ spl9_57 ),
    inference(avatar_component_clause,[],[f60566])).

fof(f60580,plain,
    ( ~ spl9_59
    | ~ spl9_57 ),
    inference(avatar_split_clause,[],[f60574,f60566,f60577])).

fof(f60574,plain,
    ( ~ r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl9_57 ),
    inference(resolution,[],[f60568,f66])).

fof(f60573,plain,
    ( spl9_57
    | spl9_58
    | ~ spl9_35 ),
    inference(avatar_split_clause,[],[f11022,f11018,f60570,f60566])).

fof(f11018,plain,
    ( spl9_35
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).

fof(f11022,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1)
    | r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))
    | ~ spl9_35 ),
    inference(resolution,[],[f11020,f55])).

fof(f11020,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))
    | ~ spl9_35 ),
    inference(avatar_component_clause,[],[f11018])).

fof(f56543,plain,
    ( spl9_56
    | ~ spl9_49
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f55829,f52973,f52876,f56540])).

fof(f52973,plain,
    ( spl9_52
  <=> r2_hidden(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).

fof(f55829,plain,
    ( r2_hidden(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl9_49
    | ~ spl9_52 ),
    inference(backward_demodulation,[],[f52975,f52878])).

fof(f52975,plain,
    ( r2_hidden(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK3))
    | ~ spl9_52 ),
    inference(avatar_component_clause,[],[f52973])).

fof(f56522,plain,
    ( ~ spl9_55
    | spl9_48
    | ~ spl9_49 ),
    inference(avatar_split_clause,[],[f56308,f52876,f52872,f56519])).

fof(f56519,plain,
    ( spl9_55
  <=> r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_55])])).

fof(f52872,plain,
    ( spl9_48
  <=> r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).

fof(f56308,plain,
    ( ~ r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | spl9_48
    | ~ spl9_49 ),
    inference(forward_demodulation,[],[f52873,f52878])).

fof(f52873,plain,
    ( ~ r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))
    | spl9_48 ),
    inference(avatar_component_clause,[],[f52872])).

fof(f55677,plain,
    ( spl9_54
    | ~ spl9_51 ),
    inference(avatar_split_clause,[],[f52927,f52888,f55674])).

fof(f55674,plain,
    ( spl9_54
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))),k2_zfmisc_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).

fof(f52888,plain,
    ( spl9_51
  <=> r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_51])])).

fof(f52927,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))),k2_zfmisc_1(sK0,sK3))
    | ~ spl9_51 ),
    inference(resolution,[],[f52890,f26029])).

fof(f52890,plain,
    ( r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK0,sK3))
    | ~ spl9_51 ),
    inference(avatar_component_clause,[],[f52888])).

fof(f53034,plain,
    ( spl9_53
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f52985,f52973,f53031])).

fof(f52985,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),k2_zfmisc_1(sK0,sK3))
    | ~ spl9_52 ),
    inference(resolution,[],[f52975,f26029])).

fof(f52976,plain,
    ( spl9_8
    | spl9_52
    | ~ spl9_25 ),
    inference(avatar_split_clause,[],[f7909,f7805,f52973,f178])).

fof(f7805,plain,
    ( spl9_25
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f7909,plain,
    ( r2_hidden(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK3))
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl9_25 ),
    inference(resolution,[],[f7811,f151])).

fof(f7811,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X1,k2_zfmisc_1(sK0,sK3)) )
    | ~ spl9_25 ),
    inference(superposition,[],[f5452,f7807])).

fof(f7807,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3)
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f7805])).

fof(f5452,plain,(
    ! [X43,X41,X42,X40] :
      ( ~ r2_hidden(X43,k2_zfmisc_1(k3_xboole_0(X40,X42),X41))
      | r2_hidden(X43,k2_zfmisc_1(X40,X41)) ) ),
    inference(superposition,[],[f90,f2057])).

fof(f2057,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0) ),
    inference(superposition,[],[f79,f52])).

fof(f52891,plain,
    ( spl9_51
    | ~ spl9_48 ),
    inference(avatar_split_clause,[],[f52881,f52872,f52888])).

fof(f52881,plain,
    ( r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK0,sK3))
    | ~ spl9_48 ),
    inference(resolution,[],[f52874,f65])).

fof(f52874,plain,
    ( r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))
    | ~ spl9_48 ),
    inference(avatar_component_clause,[],[f52872])).

fof(f52886,plain,
    ( ~ spl9_50
    | ~ spl9_48 ),
    inference(avatar_split_clause,[],[f52880,f52872,f52883])).

fof(f52880,plain,
    ( ~ r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK0,sK1))
    | ~ spl9_48 ),
    inference(resolution,[],[f52874,f66])).

fof(f52879,plain,
    ( spl9_48
    | spl9_49
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f7858,f7854,f52876,f52872])).

fof(f7854,plain,
    ( spl9_26
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f7858,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3)
    | r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))
    | ~ spl9_26 ),
    inference(resolution,[],[f7856,f55])).

fof(f7856,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f7854])).

fof(f15620,plain,
    ( spl9_6
    | spl9_47
    | ~ spl9_5
    | ~ spl9_41 ),
    inference(avatar_split_clause,[],[f14748,f11665,f112,f15618,f170])).

fof(f15618,plain,
    ( spl9_47
  <=> ! [X55] : k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X55,k3_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).

fof(f112,plain,
    ( spl9_5
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f11665,plain,
    ( spl9_41
  <=> ! [X14] : k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X14,k3_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).

fof(f14748,plain,
    ( ! [X55] :
        ( k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X55,k3_xboole_0(sK0,sK2)))
        | k1_xboole_0 = sK3 )
    | ~ spl9_5
    | ~ spl9_41 ),
    inference(trivial_inequality_removal,[],[f14722])).

fof(f14722,plain,
    ( ! [X55] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X55,k3_xboole_0(sK0,sK2)))
        | k1_xboole_0 = sK3 )
    | ~ spl9_5
    | ~ spl9_41 ),
    inference(superposition,[],[f62,f14663])).

fof(f14663,plain,
    ( ! [X3] : k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(X3,k3_xboole_0(sK0,sK2))),sK3)
    | ~ spl9_5
    | ~ spl9_41 ),
    inference(forward_demodulation,[],[f14605,f53])).

fof(f14605,plain,
    ( ! [X3] : k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(k4_xboole_0(X3,k3_xboole_0(sK0,sK2)),sK2),sK3)
    | ~ spl9_5
    | ~ spl9_41 ),
    inference(superposition,[],[f11727,f7695])).

fof(f7695,plain,
    ( ! [X4] : k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X4,sK3)) = k2_zfmisc_1(k3_xboole_0(X4,sK2),sK3)
    | ~ spl9_5 ),
    inference(superposition,[],[f5416,f53])).

fof(f5416,plain,
    ( ! [X9] : k2_zfmisc_1(k3_xboole_0(X9,sK2),sK3) = k3_xboole_0(k2_zfmisc_1(X9,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl9_5 ),
    inference(superposition,[],[f2057,f114])).

fof(f114,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f112])).

fof(f11727,plain,
    ( ! [X6,X4,X5] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,X5),k2_zfmisc_1(k4_xboole_0(X4,k3_xboole_0(sK0,sK2)),X6))
    | ~ spl9_41 ),
    inference(forward_demodulation,[],[f11691,f84])).

fof(f84,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f11691,plain,
    ( ! [X6,X4,X5] : k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X5,X6)) = k3_xboole_0(k2_zfmisc_1(sK0,X5),k2_zfmisc_1(k4_xboole_0(X4,k3_xboole_0(sK0,sK2)),X6))
    | ~ spl9_41 ),
    inference(superposition,[],[f79,f11666])).

fof(f11666,plain,
    ( ! [X14] : k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X14,k3_xboole_0(sK0,sK2)))
    | ~ spl9_41 ),
    inference(avatar_component_clause,[],[f11665])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f15093,plain,
    ( spl9_46
    | spl9_7
    | ~ spl9_5
    | ~ spl9_27 ),
    inference(avatar_split_clause,[],[f13202,f7861,f112,f174,f15091])).

fof(f15091,plain,
    ( spl9_46
  <=> ! [X54] : k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X54,k3_xboole_0(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f7861,plain,
    ( spl9_27
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f13202,plain,
    ( ! [X54] :
        ( k1_xboole_0 = sK2
        | k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X54,k3_xboole_0(sK1,sK3))) )
    | ~ spl9_5
    | ~ spl9_27 ),
    inference(trivial_inequality_removal,[],[f13177])).

fof(f13177,plain,
    ( ! [X54] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = sK2
        | k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X54,k3_xboole_0(sK1,sK3))) )
    | ~ spl9_5
    | ~ spl9_27 ),
    inference(superposition,[],[f62,f13121])).

fof(f13121,plain,
    ( ! [X9] : k1_xboole_0 = k2_zfmisc_1(sK2,k3_xboole_0(sK3,k4_xboole_0(X9,k3_xboole_0(sK1,sK3))))
    | ~ spl9_5
    | ~ spl9_27 ),
    inference(forward_demodulation,[],[f13070,f53])).

fof(f13070,plain,
    ( ! [X9] : k1_xboole_0 = k2_zfmisc_1(sK2,k3_xboole_0(k4_xboole_0(X9,k3_xboole_0(sK1,sK3)),sK3))
    | ~ spl9_5
    | ~ spl9_27 ),
    inference(superposition,[],[f7877,f4824])).

fof(f4824,plain,
    ( ! [X3] : k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X3)) = k2_zfmisc_1(sK2,k3_xboole_0(X3,sK3))
    | ~ spl9_5 ),
    inference(superposition,[],[f2949,f53])).

fof(f2949,plain,
    ( ! [X9] : k2_zfmisc_1(sK2,k3_xboole_0(X9,sK3)) = k3_xboole_0(k2_zfmisc_1(sK2,X9),k2_zfmisc_1(sK0,sK1))
    | ~ spl9_5 ),
    inference(superposition,[],[f2034,f114])).

fof(f7877,plain,
    ( ! [X12,X13] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X12,k4_xboole_0(X13,k3_xboole_0(sK1,sK3))))
    | ~ spl9_27 ),
    inference(superposition,[],[f2103,f7863])).

fof(f7863,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))
    | ~ spl9_27 ),
    inference(avatar_component_clause,[],[f7861])).

fof(f2103,plain,(
    ! [X26,X24,X23,X25] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X25,X23),k2_zfmisc_1(X26,k4_xboole_0(X24,X23))) ),
    inference(forward_demodulation,[],[f2063,f83])).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2063,plain,(
    ! [X26,X24,X23,X25] : k3_xboole_0(k2_zfmisc_1(X25,X23),k2_zfmisc_1(X26,k4_xboole_0(X24,X23))) = k2_zfmisc_1(k3_xboole_0(X25,X26),k1_xboole_0) ),
    inference(superposition,[],[f79,f713])).

fof(f713,plain,(
    ! [X24,X25] : k1_xboole_0 = k3_xboole_0(X24,k4_xboole_0(X25,X24)) ),
    inference(superposition,[],[f695,f126])).

fof(f695,plain,(
    ! [X4,X5,X3] : k3_xboole_0(X3,k4_xboole_0(X4,X3)) = k3_xboole_0(k3_xboole_0(X3,k4_xboole_0(X4,X3)),X5) ),
    inference(resolution,[],[f693,f54])).

fof(f693,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X1,k4_xboole_0(X0,X1)),X2) ),
    inference(forward_demodulation,[],[f692,f53])).

fof(f692,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(k4_xboole_0(X0,X1),X1),X2) ),
    inference(duplicate_literal_removal,[],[f675])).

fof(f675,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(k4_xboole_0(X0,X1),X1),X2)
      | r1_tarski(k3_xboole_0(k4_xboole_0(X0,X1),X1),X2) ) ),
    inference(resolution,[],[f248,f142])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(k3_xboole_0(X0,X1),X2),X0)
      | r1_tarski(k3_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f90,f56])).

fof(f248,plain,(
    ! [X19,X17,X18,X16] :
      ( ~ r2_hidden(sK4(k3_xboole_0(X16,X17),X18),k4_xboole_0(X19,X17))
      | r1_tarski(k3_xboole_0(X16,X17),X18) ) ),
    inference(resolution,[],[f136,f86])).

fof(f14938,plain,
    ( spl9_6
    | spl9_45
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f14887,f14836,f14935,f170])).

fof(f14935,plain,
    ( spl9_45
  <=> k1_xboole_0 = k4_xboole_0(sK2,k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_45])])).

fof(f14836,plain,
    ( spl9_44
  <=> k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,k3_xboole_0(sK0,sK2)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).

fof(f14887,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k3_xboole_0(sK0,sK2))
    | k1_xboole_0 = sK3
    | ~ spl9_44 ),
    inference(trivial_inequality_removal,[],[f14861])).

fof(f14861,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK2,k3_xboole_0(sK0,sK2))
    | k1_xboole_0 = sK3
    | ~ spl9_44 ),
    inference(superposition,[],[f62,f14838])).

fof(f14838,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,k3_xboole_0(sK0,sK2)),sK3)
    | ~ spl9_44 ),
    inference(avatar_component_clause,[],[f14836])).

fof(f14839,plain,
    ( spl9_44
    | ~ spl9_5
    | ~ spl9_41 ),
    inference(avatar_split_clause,[],[f14686,f11665,f112,f14836])).

fof(f14686,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,k3_xboole_0(sK0,sK2)),sK3)
    | ~ spl9_5
    | ~ spl9_41 ),
    inference(superposition,[],[f14663,f226])).

fof(f13389,plain,
    ( spl9_43
    | spl9_7
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f13338,f13289,f174,f13386])).

fof(f13289,plain,
    ( spl9_42
  <=> k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,k3_xboole_0(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f13338,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k4_xboole_0(sK3,k3_xboole_0(sK1,sK3))
    | ~ spl9_42 ),
    inference(trivial_inequality_removal,[],[f13313])).

fof(f13313,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k4_xboole_0(sK3,k3_xboole_0(sK1,sK3))
    | ~ spl9_42 ),
    inference(superposition,[],[f62,f13291])).

fof(f13291,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,k3_xboole_0(sK1,sK3)))
    | ~ spl9_42 ),
    inference(avatar_component_clause,[],[f13289])).

fof(f13292,plain,
    ( spl9_42
    | ~ spl9_5
    | ~ spl9_27 ),
    inference(avatar_split_clause,[],[f13143,f7861,f112,f13289])).

fof(f13143,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,k3_xboole_0(sK1,sK3)))
    | ~ spl9_5
    | ~ spl9_27 ),
    inference(superposition,[],[f13121,f226])).

fof(f11667,plain,
    ( spl9_2
    | spl9_41
    | ~ spl9_36 ),
    inference(avatar_split_clause,[],[f11401,f11051,f11665,f98])).

fof(f11401,plain,
    ( ! [X14] :
        ( k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X14,k3_xboole_0(sK0,sK2)))
        | k1_xboole_0 = sK1 )
    | ~ spl9_36 ),
    inference(trivial_inequality_removal,[],[f11378])).

fof(f11378,plain,
    ( ! [X14] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X14,k3_xboole_0(sK0,sK2)))
        | k1_xboole_0 = sK1 )
    | ~ spl9_36 ),
    inference(superposition,[],[f62,f11330])).

fof(f11330,plain,
    ( ! [X5] : k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,k4_xboole_0(X5,k3_xboole_0(sK0,sK2))),sK1)
    | ~ spl9_36 ),
    inference(forward_demodulation,[],[f11292,f84])).

fof(f11292,plain,
    ( ! [X5] : k2_zfmisc_1(k1_xboole_0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,k4_xboole_0(X5,k3_xboole_0(sK0,sK2))),sK1)
    | ~ spl9_36 ),
    inference(superposition,[],[f11092,f713])).

fof(f11092,plain,
    ( ! [X8] : k2_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,sK2),X8),sK1) = k2_zfmisc_1(k3_xboole_0(sK0,X8),sK1)
    | ~ spl9_36 ),
    inference(forward_demodulation,[],[f11066,f2057])).

fof(f11066,plain,
    ( ! [X8] : k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X8,sK1)) = k2_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,sK2),X8),sK1)
    | ~ spl9_36 ),
    inference(superposition,[],[f2057,f11053])).

fof(f11557,plain,
    ( spl9_2
    | spl9_40
    | ~ spl9_39 ),
    inference(avatar_split_clause,[],[f11473,f11440,f11554,f98])).

fof(f11554,plain,
    ( spl9_40
  <=> k1_xboole_0 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f11440,plain,
    ( spl9_39
  <=> k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).

fof(f11473,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | k1_xboole_0 = sK1
    | ~ spl9_39 ),
    inference(trivial_inequality_removal,[],[f11450])).

fof(f11450,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | k1_xboole_0 = sK1
    | ~ spl9_39 ),
    inference(superposition,[],[f62,f11442])).

fof(f11442,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)
    | ~ spl9_39 ),
    inference(avatar_component_clause,[],[f11440])).

fof(f11443,plain,
    ( spl9_39
    | ~ spl9_36 ),
    inference(avatar_split_clause,[],[f11369,f11051,f11440])).

fof(f11369,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)
    | ~ spl9_36 ),
    inference(superposition,[],[f11330,f226])).

fof(f11176,plain,
    ( spl9_38
    | ~ spl9_37 ),
    inference(avatar_split_clause,[],[f11145,f11116,f11173])).

fof(f11173,plain,
    ( spl9_38
  <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f11116,plain,
    ( spl9_37
  <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).

fof(f11145,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK0,sK1))
    | ~ spl9_37 ),
    inference(superposition,[],[f289,f11118])).

fof(f11118,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))
    | ~ spl9_37 ),
    inference(avatar_component_clause,[],[f11116])).

fof(f289,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f264,f53])).

fof(f264,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),X3) ),
    inference(resolution,[],[f261,f54])).

fof(f11119,plain,
    ( spl9_37
    | ~ spl9_35 ),
    inference(avatar_split_clause,[],[f11023,f11018,f11116])).

fof(f11023,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))
    | ~ spl9_35 ),
    inference(resolution,[],[f11020,f54])).

fof(f11054,plain,
    ( spl9_36
    | ~ spl9_5
    | ~ spl9_18
    | ~ spl9_33 ),
    inference(avatar_split_clause,[],[f10819,f10216,f5988,f112,f11051])).

fof(f5988,plain,
    ( spl9_18
  <=> k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f10216,plain,
    ( spl9_33
  <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).

fof(f10819,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)
    | ~ spl9_5
    | ~ spl9_18
    | ~ spl9_33 ),
    inference(backward_demodulation,[],[f5990,f10818])).

fof(f10818,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))
    | ~ spl9_5
    | ~ spl9_33 ),
    inference(forward_demodulation,[],[f10817,f289])).

fof(f10817,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK3,k3_xboole_0(sK1,sK3)))
    | ~ spl9_5
    | ~ spl9_33 ),
    inference(forward_demodulation,[],[f10776,f53])).

fof(f10776,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k3_xboole_0(k3_xboole_0(sK1,sK3),sK3))
    | ~ spl9_5
    | ~ spl9_33 ),
    inference(superposition,[],[f10218,f4824])).

fof(f10218,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))
    | ~ spl9_33 ),
    inference(avatar_component_clause,[],[f10216])).

fof(f5990,plain,
    ( k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f5988])).

fof(f11021,plain,
    ( spl9_35
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f10935,f10903,f11018])).

fof(f10935,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))
    | ~ spl9_34 ),
    inference(superposition,[],[f2976,f10905])).

fof(f2976,plain,(
    ! [X64,X62,X63] : r1_tarski(k2_zfmisc_1(X62,k3_xboole_0(X63,X64)),k2_zfmisc_1(X62,X63)) ),
    inference(superposition,[],[f266,f2034])).

fof(f10906,plain,
    ( spl9_34
    | ~ spl9_5
    | ~ spl9_33 ),
    inference(avatar_split_clause,[],[f10818,f10216,f112,f10903])).

fof(f10219,plain,
    ( spl9_33
    | ~ spl9_19 ),
    inference(avatar_split_clause,[],[f6287,f6282,f10216])).

fof(f6282,plain,
    ( spl9_19
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f6287,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))
    | ~ spl9_19 ),
    inference(resolution,[],[f6284,f54])).

fof(f6284,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f6282])).

fof(f9153,plain,
    ( spl9_32
    | spl9_1
    | ~ spl9_27 ),
    inference(avatar_split_clause,[],[f9014,f7861,f93,f9151])).

fof(f9151,plain,
    ( spl9_32
  <=> ! [X15] : k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(X15,k3_xboole_0(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f9014,plain,
    ( ! [X15] :
        ( k1_xboole_0 = sK0
        | k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(X15,k3_xboole_0(sK1,sK3))) )
    | ~ spl9_27 ),
    inference(trivial_inequality_removal,[],[f8997])).

fof(f8997,plain,
    ( ! [X15] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(X15,k3_xboole_0(sK1,sK3))) )
    | ~ spl9_27 ),
    inference(superposition,[],[f62,f8956])).

fof(f8956,plain,
    ( ! [X5] : k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(X5,k3_xboole_0(sK1,sK3))))
    | ~ spl9_27 ),
    inference(forward_demodulation,[],[f8923,f83])).

fof(f8923,plain,
    ( ! [X5] : k2_zfmisc_1(sK0,k1_xboole_0) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(X5,k3_xboole_0(sK1,sK3))))
    | ~ spl9_27 ),
    inference(superposition,[],[f7886,f713])).

fof(f7886,plain,
    ( ! [X6] : k2_zfmisc_1(sK0,k3_xboole_0(k3_xboole_0(sK1,sK3),X6)) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,X6))
    | ~ spl9_27 ),
    inference(forward_demodulation,[],[f7872,f2034])).

fof(f7872,plain,
    ( ! [X6] : k2_zfmisc_1(sK0,k3_xboole_0(k3_xboole_0(sK1,sK3),X6)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,X6))
    | ~ spl9_27 ),
    inference(superposition,[],[f2034,f7863])).

fof(f9092,plain,
    ( spl9_31
    | spl9_1
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f9072,f9044,f93,f9089])).

fof(f9044,plain,
    ( spl9_30
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,k3_xboole_0(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f9072,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK1,k3_xboole_0(sK1,sK3))
    | ~ spl9_30 ),
    inference(trivial_inequality_removal,[],[f9055])).

fof(f9055,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK1,k3_xboole_0(sK1,sK3))
    | ~ spl9_30 ),
    inference(superposition,[],[f62,f9046])).

fof(f9046,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,k3_xboole_0(sK1,sK3)))
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f9044])).

fof(f9047,plain,
    ( spl9_30
    | ~ spl9_27 ),
    inference(avatar_split_clause,[],[f8987,f7861,f9044])).

fof(f8987,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,k3_xboole_0(sK1,sK3)))
    | ~ spl9_27 ),
    inference(superposition,[],[f8956,f226])).

fof(f7979,plain,
    ( spl9_29
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f7955,f7932,f7976])).

fof(f7976,plain,
    ( spl9_29
  <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f7932,plain,
    ( spl9_28
  <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f7955,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl9_28 ),
    inference(superposition,[],[f289,f7934])).

fof(f7934,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f7932])).

fof(f7935,plain,
    ( spl9_28
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f7859,f7854,f7932])).

fof(f7859,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))
    | ~ spl9_26 ),
    inference(resolution,[],[f7856,f54])).

fof(f7864,plain,
    ( spl9_27
    | ~ spl9_5
    | ~ spl9_23 ),
    inference(avatar_split_clause,[],[f7740,f6992,f112,f7861])).

fof(f6992,plain,
    ( spl9_23
  <=> k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f7740,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))
    | ~ spl9_5
    | ~ spl9_23 ),
    inference(forward_demodulation,[],[f7739,f114])).

fof(f7739,plain,
    ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))
    | ~ spl9_5
    | ~ spl9_23 ),
    inference(forward_demodulation,[],[f7738,f52])).

fof(f7738,plain,
    ( k2_zfmisc_1(k3_xboole_0(sK2,sK2),sK3) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))
    | ~ spl9_5
    | ~ spl9_23 ),
    inference(forward_demodulation,[],[f7737,f2978])).

fof(f2978,plain,(
    ! [X70,X68,X69] : k2_zfmisc_1(X68,k3_xboole_0(X69,X70)) = k3_xboole_0(k2_zfmisc_1(X68,k3_xboole_0(X69,X70)),k2_zfmisc_1(X68,X69)) ),
    inference(superposition,[],[f273,f2034])).

fof(f7737,plain,
    ( k2_zfmisc_1(k3_xboole_0(sK2,sK2),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1))
    | ~ spl9_5
    | ~ spl9_23 ),
    inference(forward_demodulation,[],[f7687,f7029])).

fof(f7029,plain,
    ( ! [X8] : k2_zfmisc_1(k3_xboole_0(sK2,X8),sK3) = k2_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,sK2),X8),sK3)
    | ~ spl9_5
    | ~ spl9_23 ),
    inference(forward_demodulation,[],[f7028,f5410])).

fof(f5410,plain,
    ( ! [X9] : k2_zfmisc_1(k3_xboole_0(sK2,X9),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X9,sK3))
    | ~ spl9_5 ),
    inference(superposition,[],[f2057,f114])).

fof(f7028,plain,
    ( ! [X8] : k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X8,sK3)) = k2_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,sK2),X8),sK3)
    | ~ spl9_23 ),
    inference(forward_demodulation,[],[f7007,f2106])).

fof(f2106,plain,(
    ! [X30,X33,X31,X32] : k3_xboole_0(k2_zfmisc_1(X32,k3_xboole_0(X30,X31)),k2_zfmisc_1(X33,X31)) = k3_xboole_0(k2_zfmisc_1(X32,X30),k2_zfmisc_1(X33,X31)) ),
    inference(forward_demodulation,[],[f2065,f79])).

fof(f2065,plain,(
    ! [X30,X33,X31,X32] : k3_xboole_0(k2_zfmisc_1(X32,k3_xboole_0(X30,X31)),k2_zfmisc_1(X33,X31)) = k2_zfmisc_1(k3_xboole_0(X32,X33),k3_xboole_0(X30,X31)) ),
    inference(superposition,[],[f79,f264])).

fof(f7007,plain,
    ( ! [X8] : k2_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,sK2),X8),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(X8,sK3))
    | ~ spl9_23 ),
    inference(superposition,[],[f2057,f6994])).

fof(f6994,plain,
    ( k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3)
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f6992])).

fof(f7687,plain,
    ( k3_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,sK2),sK2),sK3)
    | ~ spl9_5
    | ~ spl9_23 ),
    inference(superposition,[],[f5416,f6994])).

fof(f7857,plain,
    ( spl9_26
    | ~ spl9_25 ),
    inference(avatar_split_clause,[],[f7813,f7805,f7854])).

fof(f7813,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))
    | ~ spl9_25 ),
    inference(superposition,[],[f5461,f7807])).

fof(f5461,plain,(
    ! [X74,X72,X73] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X72,X74),X73),k2_zfmisc_1(X72,X73)) ),
    inference(superposition,[],[f266,f2057])).

fof(f7808,plain,
    ( spl9_25
    | ~ spl9_5
    | ~ spl9_23 ),
    inference(avatar_split_clause,[],[f7741,f6992,f112,f7805])).

fof(f7741,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3)
    | ~ spl9_5
    | ~ spl9_23 ),
    inference(backward_demodulation,[],[f6994,f7740])).

fof(f7445,plain,
    ( spl9_24
    | ~ spl9_5
    | ~ spl9_23 ),
    inference(avatar_split_clause,[],[f7433,f6992,f112,f7442])).

fof(f7442,plain,
    ( spl9_24
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f7433,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))
    | ~ spl9_5
    | ~ spl9_23 ),
    inference(superposition,[],[f7033,f52])).

fof(f7033,plain,
    ( ! [X18] : r1_tarski(k2_zfmisc_1(sK0,k3_xboole_0(X18,sK1)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))
    | ~ spl9_5
    | ~ spl9_23 ),
    inference(forward_demodulation,[],[f7032,f2034])).

fof(f7032,plain,
    ( ! [X18] : r1_tarski(k3_xboole_0(k2_zfmisc_1(sK0,X18),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))
    | ~ spl9_5
    | ~ spl9_23 ),
    inference(forward_demodulation,[],[f7031,f114])).

fof(f7031,plain,
    ( ! [X18] : r1_tarski(k3_xboole_0(k2_zfmisc_1(sK0,X18),k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))
    | ~ spl9_23 ),
    inference(forward_demodulation,[],[f7013,f79])).

fof(f7013,plain,
    ( ! [X18] : r1_tarski(k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(X18,sK3)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))
    | ~ spl9_23 ),
    inference(superposition,[],[f2973,f6994])).

fof(f2973,plain,(
    ! [X54,X55,X53] : r1_tarski(k2_zfmisc_1(X53,k3_xboole_0(X54,X55)),k2_zfmisc_1(X53,X55)) ),
    inference(superposition,[],[f261,f2034])).

fof(f6995,plain,
    ( spl9_23
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f6674,f112,f6992])).

fof(f6674,plain,
    ( k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3)
    | ~ spl9_5 ),
    inference(forward_demodulation,[],[f6620,f53])).

fof(f6620,plain,
    ( k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK3)
    | ~ spl9_5 ),
    inference(superposition,[],[f5410,f2034])).

fof(f6924,plain,
    ( spl9_6
    | spl9_22
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f6713,f112,f6922,f170])).

fof(f6713,plain,
    ( ! [X14] :
        ( k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X14,sK0))
        | k1_xboole_0 = sK3 )
    | ~ spl9_5 ),
    inference(trivial_inequality_removal,[],[f6698])).

fof(f6698,plain,
    ( ! [X14] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X14,sK0))
        | k1_xboole_0 = sK3 )
    | ~ spl9_5 ),
    inference(superposition,[],[f62,f6623])).

fof(f6623,plain,
    ( ! [X3] : k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(X3,sK0)),sK3)
    | ~ spl9_5 ),
    inference(superposition,[],[f5410,f2083])).

fof(f2083,plain,(
    ! [X26,X24,X23,X25] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X23,X25),k2_zfmisc_1(k4_xboole_0(X24,X23),X26)) ),
    inference(forward_demodulation,[],[f2040,f84])).

fof(f2040,plain,(
    ! [X26,X24,X23,X25] : k3_xboole_0(k2_zfmisc_1(X23,X25),k2_zfmisc_1(k4_xboole_0(X24,X23),X26)) = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X25,X26)) ),
    inference(superposition,[],[f79,f713])).

fof(f6782,plain,
    ( spl9_6
    | spl9_21
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f6766,f6739,f6779,f170])).

fof(f6779,plain,
    ( spl9_21
  <=> k1_xboole_0 = k4_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f6739,plain,
    ( spl9_20
  <=> k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f6766,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK0)
    | k1_xboole_0 = sK3
    | ~ spl9_20 ),
    inference(trivial_inequality_removal,[],[f6751])).

fof(f6751,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK2,sK0)
    | k1_xboole_0 = sK3
    | ~ spl9_20 ),
    inference(superposition,[],[f62,f6741])).

fof(f6741,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3)
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f6739])).

fof(f6742,plain,
    ( spl9_20
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f6689,f112,f6739])).

fof(f6689,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3)
    | ~ spl9_5 ),
    inference(superposition,[],[f6623,f226])).

fof(f6285,plain,
    ( spl9_19
    | ~ spl9_5
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f6273,f5988,f112,f6282])).

fof(f6273,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))
    | ~ spl9_5
    | ~ spl9_18 ),
    inference(superposition,[],[f6021,f52])).

fof(f6021,plain,
    ( ! [X19] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X19,sK0),sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))
    | ~ spl9_5
    | ~ spl9_18 ),
    inference(forward_demodulation,[],[f6008,f6017])).

fof(f6017,plain,
    ( ! [X7] : k2_zfmisc_1(k3_xboole_0(X7,k3_xboole_0(sK0,sK2)),sK1) = k2_zfmisc_1(k3_xboole_0(X7,sK0),sK1)
    | ~ spl9_5
    | ~ spl9_18 ),
    inference(forward_demodulation,[],[f6016,f2057])).

fof(f6016,plain,
    ( ! [X7] : k2_zfmisc_1(k3_xboole_0(X7,k3_xboole_0(sK0,sK2)),sK1) = k3_xboole_0(k2_zfmisc_1(X7,sK1),k2_zfmisc_1(sK0,sK1))
    | ~ spl9_5
    | ~ spl9_18 ),
    inference(forward_demodulation,[],[f6015,f114])).

fof(f6015,plain,
    ( ! [X7] : k2_zfmisc_1(k3_xboole_0(X7,k3_xboole_0(sK0,sK2)),sK1) = k3_xboole_0(k2_zfmisc_1(X7,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl9_18 ),
    inference(forward_demodulation,[],[f6000,f2102])).

fof(f2102,plain,(
    ! [X17,X15,X18,X16] : k3_xboole_0(k2_zfmisc_1(X17,X15),k2_zfmisc_1(X18,k3_xboole_0(X15,X16))) = k3_xboole_0(k2_zfmisc_1(X17,X15),k2_zfmisc_1(X18,X16)) ),
    inference(forward_demodulation,[],[f2061,f79])).

fof(f2061,plain,(
    ! [X17,X15,X18,X16] : k3_xboole_0(k2_zfmisc_1(X17,X15),k2_zfmisc_1(X18,k3_xboole_0(X15,X16))) = k2_zfmisc_1(k3_xboole_0(X17,X18),k3_xboole_0(X15,X16)) ),
    inference(superposition,[],[f79,f309])).

fof(f6000,plain,
    ( ! [X7] : k2_zfmisc_1(k3_xboole_0(X7,k3_xboole_0(sK0,sK2)),sK1) = k3_xboole_0(k2_zfmisc_1(X7,sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))
    | ~ spl9_18 ),
    inference(superposition,[],[f2057,f5990])).

fof(f6008,plain,
    ( ! [X19] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X19,k3_xboole_0(sK0,sK2)),sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))
    | ~ spl9_18 ),
    inference(superposition,[],[f5458,f5990])).

fof(f5458,plain,(
    ! [X64,X65,X63] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X63,X65),X64),k2_zfmisc_1(X65,X64)) ),
    inference(superposition,[],[f261,f2057])).

fof(f5991,plain,
    ( spl9_18
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f5501,f112,f5988])).

fof(f5501,plain,
    ( k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)
    | ~ spl9_5 ),
    inference(forward_demodulation,[],[f5426,f53])).

fof(f5426,plain,
    ( k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK1)
    | ~ spl9_5 ),
    inference(superposition,[],[f2057,f2949])).

fof(f5926,plain,
    ( spl9_2
    | spl9_17
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f5802,f112,f5924,f98])).

fof(f5802,plain,
    ( ! [X8] :
        ( k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X8,sK2))
        | k1_xboole_0 = sK1 )
    | ~ spl9_5 ),
    inference(trivial_inequality_removal,[],[f5787])).

fof(f5787,plain,
    ( ! [X8] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X8,sK2))
        | k1_xboole_0 = sK1 )
    | ~ spl9_5 ),
    inference(superposition,[],[f62,f5422])).

fof(f5422,plain,
    ( ! [X11] : k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,k4_xboole_0(X11,sK2)),sK1)
    | ~ spl9_5 ),
    inference(superposition,[],[f2057,f2172])).

fof(f2172,plain,
    ( ! [X12,X13] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(X12,sK2),X13))
    | ~ spl9_5 ),
    inference(superposition,[],[f2083,f114])).

fof(f5866,plain,
    ( spl9_2
    | spl9_16
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f5851,f5825,f5863,f98])).

fof(f5825,plain,
    ( spl9_15
  <=> k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f5851,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | k1_xboole_0 = sK1
    | ~ spl9_15 ),
    inference(trivial_inequality_removal,[],[f5836])).

fof(f5836,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | k1_xboole_0 = sK1
    | ~ spl9_15 ),
    inference(superposition,[],[f62,f5827])).

fof(f5827,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f5825])).

fof(f5828,plain,
    ( spl9_15
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f5782,f112,f5825])).

fof(f5782,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl9_5 ),
    inference(superposition,[],[f5422,f226])).

fof(f4366,plain,
    ( spl9_6
    | spl9_7
    | ~ spl9_8
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f4091,f112,f178,f174,f170])).

fof(f4091,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ spl9_5 ),
    inference(superposition,[],[f62,f114])).

fof(f4272,plain,
    ( spl9_2
    | spl9_1
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f4266,f178,f93,f98])).

fof(f4266,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl9_8 ),
    inference(trivial_inequality_removal,[],[f4256])).

fof(f4256,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl9_8 ),
    inference(superposition,[],[f62,f179])).

fof(f179,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f178])).

fof(f4175,plain,
    ( spl9_14
    | spl9_7
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f3874,f112,f174,f4173])).

fof(f4173,plain,
    ( spl9_14
  <=> ! [X8] : k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X8,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f3874,plain,
    ( ! [X8] :
        ( k1_xboole_0 = sK2
        | k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X8,sK1)) )
    | ~ spl9_5 ),
    inference(trivial_inequality_removal,[],[f3864])).

fof(f3864,plain,
    ( ! [X8] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = sK2
        | k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X8,sK1)) )
    | ~ spl9_5 ),
    inference(superposition,[],[f62,f3810])).

fof(f3810,plain,
    ( ! [X3] : k1_xboole_0 = k2_zfmisc_1(sK2,k3_xboole_0(sK3,k4_xboole_0(X3,sK1)))
    | ~ spl9_5 ),
    inference(superposition,[],[f2945,f2103])).

fof(f2945,plain,
    ( ! [X9] : k2_zfmisc_1(sK2,k3_xboole_0(sK3,X9)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X9))
    | ~ spl9_5 ),
    inference(superposition,[],[f2034,f114])).

fof(f4047,plain,
    ( spl9_8
    | ~ spl9_5
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f3965,f174,f112,f178])).

fof(f3965,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl9_5
    | ~ spl9_7 ),
    inference(forward_demodulation,[],[f3926,f84])).

fof(f3926,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,sK3)
    | ~ spl9_5
    | ~ spl9_7 ),
    inference(backward_demodulation,[],[f114,f176])).

fof(f176,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f174])).

fof(f3924,plain,
    ( spl9_13
    | spl9_7
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f3913,f3893,f174,f3921])).

fof(f3893,plain,
    ( spl9_12
  <=> k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f3913,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k4_xboole_0(sK3,sK1)
    | ~ spl9_12 ),
    inference(trivial_inequality_removal,[],[f3903])).

fof(f3903,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k4_xboole_0(sK3,sK1)
    | ~ spl9_12 ),
    inference(superposition,[],[f62,f3895])).

fof(f3895,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1))
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f3893])).

fof(f3896,plain,
    ( spl9_12
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f3857,f112,f3893])).

fof(f3857,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1))
    | ~ spl9_5 ),
    inference(superposition,[],[f3810,f226])).

fof(f3323,plain,
    ( spl9_11
    | spl9_1
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f3225,f112,f93,f3321])).

fof(f3225,plain,
    ( ! [X2] :
        ( k1_xboole_0 = sK0
        | k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(X2,sK3)) )
    | ~ spl9_5 ),
    inference(trivial_inequality_removal,[],[f3215])).

fof(f3215,plain,
    ( ! [X2] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(X2,sK3)) )
    | ~ spl9_5 ),
    inference(superposition,[],[f62,f2950])).

fof(f2950,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(X0,sK3)))
    | ~ spl9_5 ),
    inference(superposition,[],[f2034,f2256])).

fof(f2256,plain,
    ( ! [X12,X13] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X12,k4_xboole_0(X13,sK3)))
    | ~ spl9_5 ),
    inference(superposition,[],[f2103,f114])).

fof(f3271,plain,
    ( spl9_10
    | spl9_1
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f3261,f3242,f93,f3268])).

fof(f3242,plain,
    ( spl9_9
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f3261,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK1,sK3)
    | ~ spl9_9 ),
    inference(trivial_inequality_removal,[],[f3251])).

fof(f3251,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK1,sK3)
    | ~ spl9_9 ),
    inference(superposition,[],[f62,f3244])).

fof(f3244,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f3242])).

fof(f3245,plain,
    ( spl9_9
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f3212,f112,f3242])).

fof(f3212,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))
    | ~ spl9_5 ),
    inference(superposition,[],[f2950,f226])).

fof(f181,plain,
    ( spl9_6
    | spl9_7
    | ~ spl9_8
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f168,f112,f178,f174,f170])).

fof(f168,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ spl9_5 ),
    inference(superposition,[],[f62,f114])).

fof(f115,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f47,f112])).

fof(f47,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( sK1 != sK3
      | sK0 != sK2 )
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) )
   => ( ( sK1 != sK3
        | sK0 != sK2 )
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f110,plain,
    ( ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f50,f107,f103])).

fof(f50,plain,
    ( sK1 != sK3
    | sK0 != sK2 ),
    inference(cnf_transformation,[],[f26])).

fof(f101,plain,(
    ~ spl9_2 ),
    inference(avatar_split_clause,[],[f49,f98])).

fof(f49,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f96,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f48,f93])).

fof(f48,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:19:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (26780)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.49  % (26756)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.50  % (26755)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (26763)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (26752)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (26782)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (26757)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (26776)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (26753)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (26753)Refutation not found, incomplete strategy% (26753)------------------------------
% 0.20/0.53  % (26753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26753)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (26753)Memory used [KB]: 10746
% 0.20/0.53  % (26753)Time elapsed: 0.117 s
% 0.20/0.53  % (26753)------------------------------
% 0.20/0.53  % (26753)------------------------------
% 0.20/0.53  % (26776)Refutation not found, incomplete strategy% (26776)------------------------------
% 0.20/0.53  % (26776)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26776)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (26776)Memory used [KB]: 1791
% 0.20/0.53  % (26776)Time elapsed: 0.082 s
% 0.20/0.53  % (26776)------------------------------
% 0.20/0.53  % (26776)------------------------------
% 0.20/0.53  % (26767)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (26751)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (26751)Refutation not found, incomplete strategy% (26751)------------------------------
% 0.20/0.53  % (26751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26751)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (26751)Memory used [KB]: 1663
% 0.20/0.53  % (26751)Time elapsed: 0.127 s
% 0.20/0.53  % (26751)------------------------------
% 0.20/0.53  % (26751)------------------------------
% 0.20/0.53  % (26758)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (26761)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (26779)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (26777)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (26774)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (26773)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (26768)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (26770)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (26759)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.42/0.54  % (26781)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.42/0.55  % (26769)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.42/0.55  % (26766)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.42/0.55  % (26771)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.42/0.55  % (26759)Refutation not found, incomplete strategy% (26759)------------------------------
% 1.42/0.55  % (26759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (26759)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (26759)Memory used [KB]: 10746
% 1.42/0.55  % (26759)Time elapsed: 0.150 s
% 1.42/0.55  % (26759)------------------------------
% 1.42/0.55  % (26759)------------------------------
% 1.42/0.55  % (26769)Refutation not found, incomplete strategy% (26769)------------------------------
% 1.42/0.55  % (26769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (26760)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.42/0.56  % (26754)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.42/0.56  % (26769)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (26769)Memory used [KB]: 10618
% 1.42/0.56  % (26769)Time elapsed: 0.151 s
% 1.42/0.56  % (26769)------------------------------
% 1.42/0.56  % (26769)------------------------------
% 1.42/0.56  % (26774)Refutation not found, incomplete strategy% (26774)------------------------------
% 1.42/0.56  % (26774)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (26774)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (26774)Memory used [KB]: 10746
% 1.42/0.56  % (26774)Time elapsed: 0.151 s
% 1.42/0.56  % (26774)------------------------------
% 1.42/0.56  % (26774)------------------------------
% 1.42/0.56  % (26773)Refutation not found, incomplete strategy% (26773)------------------------------
% 1.42/0.56  % (26773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (26773)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (26773)Memory used [KB]: 1791
% 1.42/0.56  % (26773)Time elapsed: 0.160 s
% 1.42/0.56  % (26773)------------------------------
% 1.42/0.56  % (26773)------------------------------
% 1.42/0.56  % (26764)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.42/0.56  % (26762)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.59/0.57  % (26778)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.59/0.57  % (26772)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.59/0.58  % (26772)Refutation not found, incomplete strategy% (26772)------------------------------
% 1.59/0.58  % (26772)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.59  % (26772)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.59  
% 1.59/0.59  % (26772)Memory used [KB]: 10746
% 1.59/0.59  % (26772)Time elapsed: 0.186 s
% 1.59/0.59  % (26772)------------------------------
% 1.59/0.59  % (26772)------------------------------
% 2.00/0.65  % (26862)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.00/0.65  % (26862)Refutation not found, incomplete strategy% (26862)------------------------------
% 2.00/0.65  % (26862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.65  % (26862)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.65  
% 2.00/0.65  % (26862)Memory used [KB]: 6268
% 2.00/0.65  % (26862)Time elapsed: 0.095 s
% 2.00/0.65  % (26862)------------------------------
% 2.00/0.65  % (26862)------------------------------
% 2.26/0.67  % (26864)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.26/0.67  % (26884)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.26/0.68  % (26876)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.26/0.69  % (26877)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.26/0.69  % (26888)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.26/0.70  % (26883)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.26/0.72  % (26906)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.86/0.79  % (26928)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 3.27/0.83  % (26756)Time limit reached!
% 3.27/0.83  % (26756)------------------------------
% 3.27/0.83  % (26756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.27/0.84  % (26756)Termination reason: Time limit
% 3.27/0.84  
% 3.27/0.84  % (26756)Memory used [KB]: 11001
% 3.27/0.84  % (26756)Time elapsed: 0.427 s
% 3.27/0.84  % (26756)------------------------------
% 3.27/0.84  % (26756)------------------------------
% 3.44/0.91  % (26752)Time limit reached!
% 3.44/0.91  % (26752)------------------------------
% 3.44/0.91  % (26752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.44/0.91  % (26752)Termination reason: Time limit
% 3.44/0.91  % (26752)Termination phase: Saturation
% 3.44/0.91  
% 3.44/0.91  % (26752)Memory used [KB]: 8699
% 3.44/0.91  % (26752)Time elapsed: 0.500 s
% 3.44/0.91  % (26752)------------------------------
% 3.44/0.91  % (26752)------------------------------
% 3.81/0.93  % (26761)Time limit reached!
% 3.81/0.93  % (26761)------------------------------
% 3.81/0.93  % (26761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.81/0.93  % (26761)Termination reason: Time limit
% 3.81/0.93  
% 3.81/0.93  % (26761)Memory used [KB]: 18933
% 3.81/0.93  % (26761)Time elapsed: 0.521 s
% 3.81/0.93  % (26761)------------------------------
% 3.81/0.93  % (26761)------------------------------
% 3.81/0.94  % (26763)Time limit reached!
% 3.81/0.94  % (26763)------------------------------
% 3.81/0.94  % (26763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.81/0.94  % (26763)Termination reason: Time limit
% 3.81/0.94  
% 3.81/0.94  % (26763)Memory used [KB]: 8315
% 3.81/0.94  % (26763)Time elapsed: 0.535 s
% 3.81/0.94  % (26763)------------------------------
% 3.81/0.94  % (26763)------------------------------
% 4.03/0.97  % (26980)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 4.03/0.99  % (26877)Time limit reached!
% 4.03/0.99  % (26877)------------------------------
% 4.03/0.99  % (26877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/0.99  % (26877)Termination reason: Time limit
% 4.03/0.99  
% 4.03/0.99  % (26877)Memory used [KB]: 7675
% 4.03/0.99  % (26877)Time elapsed: 0.417 s
% 4.03/0.99  % (26877)------------------------------
% 4.03/0.99  % (26877)------------------------------
% 4.03/1.00  % (26883)Time limit reached!
% 4.03/1.00  % (26883)------------------------------
% 4.03/1.00  % (26883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/1.00  % (26883)Termination reason: Time limit
% 4.03/1.00  
% 4.03/1.00  % (26883)Memory used [KB]: 13432
% 4.03/1.00  % (26883)Time elapsed: 0.419 s
% 4.03/1.00  % (26883)------------------------------
% 4.03/1.00  % (26883)------------------------------
% 4.03/1.02  % (26768)Time limit reached!
% 4.03/1.02  % (26768)------------------------------
% 4.03/1.02  % (26768)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/1.02  % (26768)Termination reason: Time limit
% 4.03/1.02  
% 4.03/1.02  % (26768)Memory used [KB]: 16758
% 4.03/1.02  % (26768)Time elapsed: 0.621 s
% 4.03/1.02  % (26768)------------------------------
% 4.03/1.02  % (26768)------------------------------
% 4.03/1.02  % (26781)Time limit reached!
% 4.03/1.02  % (26781)------------------------------
% 4.03/1.02  % (26781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/1.02  % (26781)Termination reason: Time limit
% 4.03/1.02  % (26781)Termination phase: Saturation
% 4.03/1.02  
% 4.03/1.02  % (26781)Memory used [KB]: 9850
% 4.03/1.02  % (26781)Time elapsed: 0.600 s
% 4.03/1.02  % (26781)------------------------------
% 4.03/1.02  % (26781)------------------------------
% 4.03/1.03  % (27012)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 4.63/1.05  % (27009)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 4.63/1.05  % (27009)Refutation not found, incomplete strategy% (27009)------------------------------
% 4.63/1.05  % (27009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.63/1.05  % (27009)Termination reason: Refutation not found, incomplete strategy
% 4.63/1.05  
% 4.63/1.05  % (27009)Memory used [KB]: 6268
% 4.63/1.05  % (27009)Time elapsed: 0.106 s
% 4.63/1.05  % (27009)------------------------------
% 4.63/1.05  % (27009)------------------------------
% 4.63/1.05  % (27010)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 4.63/1.05  % (27010)Refutation not found, incomplete strategy% (27010)------------------------------
% 4.63/1.05  % (27010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.63/1.05  % (27010)Termination reason: Refutation not found, incomplete strategy
% 4.63/1.05  
% 4.63/1.05  % (27010)Memory used [KB]: 1791
% 4.63/1.05  % (27010)Time elapsed: 0.107 s
% 4.63/1.05  % (27010)------------------------------
% 4.63/1.05  % (27010)------------------------------
% 4.63/1.07  % (26758)Time limit reached!
% 4.63/1.07  % (26758)------------------------------
% 4.63/1.07  % (26758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.63/1.07  % (26758)Termination reason: Time limit
% 4.63/1.07  
% 4.63/1.07  % (26758)Memory used [KB]: 11257
% 4.63/1.07  % (26758)Time elapsed: 0.628 s
% 4.63/1.07  % (26758)------------------------------
% 4.63/1.07  % (26758)------------------------------
% 5.65/1.10  % (27014)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 5.65/1.13  % (27013)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 5.65/1.13  % (27013)Refutation not found, incomplete strategy% (27013)------------------------------
% 5.65/1.13  % (27013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.65/1.13  % (27013)Termination reason: Refutation not found, incomplete strategy
% 5.65/1.13  
% 5.65/1.13  % (27013)Memory used [KB]: 1791
% 5.65/1.13  % (27013)Time elapsed: 0.120 s
% 5.65/1.13  % (27013)------------------------------
% 5.65/1.13  % (27013)------------------------------
% 5.65/1.14  % (27015)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 6.12/1.14  % (27015)Refutation not found, incomplete strategy% (27015)------------------------------
% 6.12/1.14  % (27015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.12/1.14  % (27015)Termination reason: Refutation not found, incomplete strategy
% 6.12/1.14  
% 6.12/1.14  % (27015)Memory used [KB]: 6268
% 6.12/1.14  % (27015)Time elapsed: 0.106 s
% 6.12/1.14  % (27015)------------------------------
% 6.12/1.14  % (27015)------------------------------
% 6.12/1.15  % (27016)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 6.35/1.18  % (27017)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 6.35/1.19  % (27018)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 6.35/1.19  % (27019)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 6.94/1.26  % (27021)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 6.94/1.26  % (27020)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 7.78/1.44  % (27016)Time limit reached!
% 7.78/1.44  % (27016)------------------------------
% 7.78/1.44  % (27016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.78/1.44  % (27016)Termination reason: Time limit
% 7.78/1.44  
% 7.78/1.44  % (27016)Memory used [KB]: 4349
% 7.78/1.44  % (27016)Time elapsed: 0.406 s
% 7.78/1.44  % (27016)------------------------------
% 7.78/1.44  % (27016)------------------------------
% 8.51/1.50  % (27012)Time limit reached!
% 8.51/1.50  % (27012)------------------------------
% 8.51/1.50  % (27012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.51/1.50  % (27012)Termination reason: Time limit
% 8.51/1.50  
% 8.51/1.50  % (27012)Memory used [KB]: 4733
% 8.51/1.50  % (27012)Time elapsed: 0.515 s
% 8.51/1.50  % (27012)------------------------------
% 8.51/1.50  % (27012)------------------------------
% 8.51/1.51  % (27019)Time limit reached!
% 8.51/1.51  % (27019)------------------------------
% 8.51/1.51  % (27019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.51/1.52  % (27019)Termination reason: Time limit
% 8.51/1.52  
% 8.51/1.52  % (27019)Memory used [KB]: 2558
% 8.51/1.52  % (27019)Time elapsed: 0.412 s
% 8.51/1.52  % (27019)------------------------------
% 8.51/1.52  % (27019)------------------------------
% 9.21/1.56  % (27022)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 10.03/1.64  % (27023)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 10.03/1.66  % (26779)Time limit reached!
% 10.03/1.66  % (26779)------------------------------
% 10.03/1.66  % (26779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.03/1.66  % (27025)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 10.03/1.67  % (26779)Termination reason: Time limit
% 10.03/1.67  
% 10.03/1.67  % (26779)Memory used [KB]: 24818
% 10.03/1.67  % (26779)Time elapsed: 1.215 s
% 10.03/1.67  % (26779)------------------------------
% 10.03/1.67  % (26779)------------------------------
% 10.42/1.70  % (26777)Time limit reached!
% 10.42/1.70  % (26777)------------------------------
% 10.42/1.70  % (26777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.42/1.70  % (26777)Termination reason: Time limit
% 10.42/1.70  % (26777)Termination phase: Saturation
% 10.42/1.70  
% 10.42/1.70  % (26777)Memory used [KB]: 20596
% 10.42/1.70  % (26777)Time elapsed: 1.300 s
% 10.42/1.70  % (26777)------------------------------
% 10.42/1.70  % (26777)------------------------------
% 11.11/1.77  % (26767)Time limit reached!
% 11.11/1.77  % (26767)------------------------------
% 11.11/1.77  % (26767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.11/1.77  % (26767)Termination reason: Time limit
% 11.11/1.77  % (26767)Termination phase: Saturation
% 11.11/1.77  
% 11.11/1.77  % (26767)Memory used [KB]: 19445
% 11.11/1.77  % (26767)Time elapsed: 1.300 s
% 11.11/1.78  % (26767)------------------------------
% 11.11/1.78  % (26767)------------------------------
% 11.11/1.78  % (27026)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 11.11/1.78  % (27026)Refutation not found, incomplete strategy% (27026)------------------------------
% 11.11/1.78  % (27026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.11/1.78  % (27026)Termination reason: Refutation not found, incomplete strategy
% 11.11/1.78  
% 11.11/1.78  % (27026)Memory used [KB]: 6268
% 11.11/1.78  % (27026)Time elapsed: 0.080 s
% 11.11/1.78  % (27026)------------------------------
% 11.11/1.78  % (27026)------------------------------
% 11.47/1.83  % (26888)Time limit reached!
% 11.47/1.83  % (26888)------------------------------
% 11.47/1.83  % (26888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.47/1.83  % (26888)Termination reason: Time limit
% 11.47/1.83  
% 11.47/1.83  % (26888)Memory used [KB]: 13560
% 11.47/1.83  % (26888)Time elapsed: 1.228 s
% 11.47/1.83  % (26888)------------------------------
% 11.47/1.83  % (26888)------------------------------
% 11.47/1.83  % (27027)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 11.70/1.88  % (27028)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 11.70/1.89  % (27028)Refutation not found, incomplete strategy% (27028)------------------------------
% 11.70/1.89  % (27028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.70/1.90  % (27028)Termination reason: Refutation not found, incomplete strategy
% 11.70/1.90  
% 11.70/1.90  % (27028)Memory used [KB]: 10746
% 11.70/1.90  % (27028)Time elapsed: 0.089 s
% 11.70/1.90  % (27028)------------------------------
% 11.70/1.90  % (27028)------------------------------
% 11.70/1.90  % (26780)Time limit reached!
% 11.70/1.90  % (26780)------------------------------
% 11.70/1.90  % (26780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.70/1.90  % (26780)Termination reason: Time limit
% 11.70/1.90  % (26780)Termination phase: Saturation
% 11.70/1.90  
% 11.70/1.90  % (26780)Memory used [KB]: 17142
% 11.70/1.90  % (26780)Time elapsed: 1.500 s
% 11.70/1.90  % (26780)------------------------------
% 11.70/1.90  % (26780)------------------------------
% 12.35/1.97  % (26755)Time limit reached!
% 12.35/1.97  % (26755)------------------------------
% 12.35/1.97  % (26755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.35/1.98  % (26755)Termination reason: Time limit
% 12.35/1.98  
% 12.35/1.98  % (26755)Memory used [KB]: 24946
% 12.35/1.98  % (26755)Time elapsed: 1.525 s
% 12.35/1.98  % (26755)------------------------------
% 12.35/1.98  % (26755)------------------------------
% 12.76/2.00  % (27025)Time limit reached!
% 12.76/2.00  % (27025)------------------------------
% 12.76/2.00  % (27025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.76/2.00  % (27025)Termination reason: Time limit
% 12.76/2.00  % (27025)Termination phase: Saturation
% 12.76/2.00  
% 12.76/2.00  % (27025)Memory used [KB]: 10490
% 12.76/2.00  % (27025)Time elapsed: 0.400 s
% 12.76/2.00  % (27025)------------------------------
% 12.76/2.00  % (27025)------------------------------
% 12.76/2.02  % (26762)Time limit reached!
% 12.76/2.02  % (26762)------------------------------
% 12.76/2.02  % (26762)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.76/2.02  % (26762)Termination reason: Time limit
% 12.76/2.02  % (26762)Termination phase: Saturation
% 12.76/2.02  
% 12.76/2.02  % (26762)Memory used [KB]: 34541
% 12.76/2.02  % (26762)Time elapsed: 1.600 s
% 12.76/2.02  % (26762)------------------------------
% 12.76/2.02  % (26762)------------------------------
% 13.82/2.14  % (27027)Time limit reached!
% 13.82/2.14  % (27027)------------------------------
% 13.82/2.14  % (27027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.20/2.16  % (27027)Termination reason: Time limit
% 14.20/2.16  % (27027)Termination phase: Saturation
% 14.20/2.16  
% 14.20/2.16  % (27027)Memory used [KB]: 12537
% 14.20/2.16  % (27027)Time elapsed: 0.400 s
% 14.20/2.16  % (27027)------------------------------
% 14.20/2.16  % (27027)------------------------------
% 14.20/2.22  % (26766)Time limit reached!
% 14.20/2.22  % (26766)------------------------------
% 14.20/2.22  % (26766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.88/2.24  % (26766)Termination reason: Time limit
% 14.88/2.24  
% 14.88/2.24  % (26766)Memory used [KB]: 6652
% 14.88/2.24  % (26766)Time elapsed: 1.808 s
% 14.88/2.24  % (26766)------------------------------
% 14.88/2.24  % (26766)------------------------------
% 15.31/2.31  % (26876)Time limit reached!
% 15.31/2.31  % (26876)------------------------------
% 15.31/2.31  % (26876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.31/2.31  % (26876)Termination reason: Time limit
% 15.31/2.31  % (26876)Termination phase: Saturation
% 15.31/2.31  
% 15.31/2.31  % (26876)Memory used [KB]: 25585
% 15.31/2.31  % (26876)Time elapsed: 1.700 s
% 15.31/2.31  % (26876)------------------------------
% 15.31/2.31  % (26876)------------------------------
% 15.93/2.39  % (27018)Time limit reached!
% 15.93/2.39  % (27018)------------------------------
% 15.93/2.39  % (27018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.29/2.41  % (27018)Termination reason: Time limit
% 16.29/2.41  
% 16.29/2.41  % (27018)Memory used [KB]: 9722
% 16.29/2.41  % (27018)Time elapsed: 1.319 s
% 16.29/2.41  % (27018)------------------------------
% 16.29/2.41  % (27018)------------------------------
% 16.29/2.42  % (26757)Time limit reached!
% 16.29/2.42  % (26757)------------------------------
% 16.29/2.42  % (26757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.29/2.43  % (26770)Time limit reached!
% 16.29/2.43  % (26770)------------------------------
% 16.29/2.43  % (26770)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.29/2.43  % (26770)Termination reason: Time limit
% 16.29/2.43  
% 16.29/2.43  % (26770)Memory used [KB]: 12920
% 16.29/2.43  % (26770)Time elapsed: 2.022 s
% 16.29/2.43  % (26770)------------------------------
% 16.29/2.43  % (26770)------------------------------
% 16.29/2.43  % (26757)Termination reason: Time limit
% 16.29/2.43  
% 16.29/2.43  % (26757)Memory used [KB]: 28784
% 16.29/2.43  % (26757)Time elapsed: 2.017 s
% 16.29/2.43  % (26757)------------------------------
% 16.29/2.43  % (26757)------------------------------
% 16.29/2.44  % (26928)Time limit reached!
% 16.29/2.44  % (26928)------------------------------
% 16.29/2.44  % (26928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.29/2.44  % (26928)Termination reason: Time limit
% 16.29/2.44  
% 16.29/2.44  % (26928)Memory used [KB]: 19573
% 16.29/2.44  % (26928)Time elapsed: 1.727 s
% 16.29/2.44  % (26928)------------------------------
% 16.29/2.44  % (26928)------------------------------
% 20.70/3.00  % (26771)Time limit reached!
% 20.70/3.00  % (26771)------------------------------
% 20.70/3.00  % (26771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.14/3.01  % (26771)Termination reason: Time limit
% 21.14/3.01  % (26771)Termination phase: Saturation
% 21.14/3.01  
% 21.14/3.01  % (26771)Memory used [KB]: 32750
% 21.14/3.01  % (26771)Time elapsed: 2.600 s
% 21.14/3.01  % (26771)------------------------------
% 21.14/3.01  % (26771)------------------------------
% 23.89/3.42  % (26864)Time limit reached!
% 23.89/3.42  % (26864)------------------------------
% 23.89/3.42  % (26864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.89/3.43  % (26864)Termination reason: Time limit
% 23.89/3.43  
% 23.89/3.43  % (26864)Memory used [KB]: 32366
% 23.89/3.43  % (26864)Time elapsed: 2.848 s
% 23.89/3.43  % (26864)------------------------------
% 23.89/3.43  % (26864)------------------------------
% 23.89/3.43  % (26764)Time limit reached!
% 23.89/3.43  % (26764)------------------------------
% 23.89/3.43  % (26764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.89/3.43  % (26764)Termination reason: Time limit
% 23.89/3.43  % (26764)Termination phase: Saturation
% 23.89/3.43  
% 23.89/3.43  % (26764)Memory used [KB]: 25458
% 23.89/3.43  % (26764)Time elapsed: 3.0000 s
% 23.89/3.43  % (26764)------------------------------
% 23.89/3.43  % (26764)------------------------------
% 31.12/4.32  % (26782)Time limit reached!
% 31.12/4.32  % (26782)------------------------------
% 31.12/4.32  % (26782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.12/4.32  % (26782)Termination reason: Time limit
% 31.12/4.32  % (26782)Termination phase: Saturation
% 31.12/4.32  
% 31.12/4.32  % (26782)Memory used [KB]: 44903
% 31.12/4.32  % (26782)Time elapsed: 3.900 s
% 31.12/4.32  % (26782)------------------------------
% 31.12/4.32  % (26782)------------------------------
% 33.45/4.57  % (27014)Time limit reached!
% 33.45/4.57  % (27014)------------------------------
% 33.45/4.57  % (27014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 33.45/4.57  % (27014)Termination reason: Time limit
% 33.45/4.57  
% 33.45/4.57  % (27014)Memory used [KB]: 68186
% 33.45/4.57  % (27014)Time elapsed: 3.528 s
% 33.45/4.57  % (27014)------------------------------
% 33.45/4.57  % (27014)------------------------------
% 36.88/5.00  % (26760)Time limit reached!
% 36.88/5.00  % (26760)------------------------------
% 36.88/5.00  % (26760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 36.88/5.01  % (26760)Termination reason: Time limit
% 36.88/5.01  % (26760)Termination phase: Saturation
% 36.88/5.01  
% 36.88/5.01  % (26760)Memory used [KB]: 50148
% 36.88/5.01  % (26760)Time elapsed: 4.600 s
% 36.88/5.01  % (26760)------------------------------
% 36.88/5.01  % (26760)------------------------------
% 41.74/5.61  % (26754)Time limit reached!
% 41.74/5.61  % (26754)------------------------------
% 41.74/5.61  % (26754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 41.74/5.61  % (26754)Termination reason: Time limit
% 41.74/5.61  
% 41.74/5.61  % (26754)Memory used [KB]: 59487
% 41.74/5.61  % (26754)Time elapsed: 5.209 s
% 41.74/5.61  % (26754)------------------------------
% 41.74/5.61  % (26754)------------------------------
% 44.14/5.92  % (27020)Refutation found. Thanks to Tanya!
% 44.14/5.92  % SZS status Theorem for theBenchmark
% 44.14/5.92  % SZS output start Proof for theBenchmark
% 44.14/5.92  fof(f144730,plain,(
% 44.14/5.92    $false),
% 44.14/5.92    inference(avatar_sat_refutation,[],[f96,f101,f110,f115,f181,f3245,f3271,f3323,f3896,f3924,f4047,f4175,f4272,f4366,f5828,f5866,f5926,f5991,f6285,f6742,f6782,f6924,f6995,f7445,f7808,f7857,f7864,f7935,f7979,f9047,f9092,f9153,f10219,f10906,f11021,f11054,f11119,f11176,f11443,f11557,f11667,f13292,f13389,f14839,f14938,f15093,f15620,f52879,f52886,f52891,f52976,f53034,f55677,f56522,f56543,f60573,f60580,f60585,f62746,f66307,f67303,f69554,f69624,f69718,f70369,f75656,f76269,f76274,f76279,f77183,f78251,f78258,f79656,f79678,f81049,f81063,f81066,f81293,f81300,f81305,f81458,f81581,f81637,f81638,f81643,f81748,f82952,f82957,f82972,f83073,f83168,f83327,f83349,f85173,f89398,f90288,f93954,f94893,f94898,f95094,f95099,f96457,f96473,f96580,f96680,f96696,f97204,f97209,f98046,f98051,f98055,f98060,f98577,f98581,f98586,f102128,f105943,f116207,f116736,f116743,f117252,f117401,f117408,f117413,f117426,f117441,f117828,f118016,f118920,f118934,f121507,f121982,f122820,f126346,f126950,f127795,f127800,f128301,f128605,f128610,f129047,f129050,f129083,f129088,f129486,f129616,f129684,f129755,f129824,f131409,f134281,f135202,f136503,f139264,f139300,f139431,f139464,f139469,f144307,f144343,f144710,f144722])).
% 44.14/5.92  fof(f144722,plain,(
% 44.14/5.92    ~spl9_149),
% 44.14/5.92    inference(avatar_contradiction_clause,[],[f144711])).
% 44.14/5.92  fof(f144711,plain,(
% 44.14/5.92    $false | ~spl9_149),
% 44.14/5.92    inference(resolution,[],[f144709,f123])).
% 44.14/5.92  fof(f123,plain,(
% 44.14/5.92    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 44.14/5.92    inference(superposition,[],[f121,f51])).
% 44.14/5.92  fof(f51,plain,(
% 44.14/5.92    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 44.14/5.92    inference(cnf_transformation,[],[f9])).
% 44.14/5.92  fof(f9,axiom,(
% 44.14/5.92    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 44.14/5.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 44.14/5.92  fof(f121,plain,(
% 44.14/5.92    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X0)))) )),
% 44.14/5.92    inference(resolution,[],[f86,f81])).
% 44.14/5.92  fof(f81,plain,(
% 44.14/5.92    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 44.14/5.92    inference(equality_resolution,[],[f80])).
% 44.14/5.92  fof(f80,plain,(
% 44.14/5.92    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 44.14/5.92    inference(equality_resolution,[],[f59])).
% 44.14/5.92  fof(f59,plain,(
% 44.14/5.92    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 44.14/5.92    inference(cnf_transformation,[],[f32])).
% 44.14/5.92  fof(f32,plain,(
% 44.14/5.92    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 44.14/5.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).
% 44.14/5.92  fof(f31,plain,(
% 44.14/5.92    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 44.14/5.92    introduced(choice_axiom,[])).
% 44.14/5.92  fof(f30,plain,(
% 44.14/5.92    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 44.14/5.92    inference(rectify,[],[f29])).
% 44.14/5.92  fof(f29,plain,(
% 44.14/5.92    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 44.14/5.92    inference(nnf_transformation,[],[f10])).
% 44.14/5.92  fof(f10,axiom,(
% 44.14/5.92    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 44.14/5.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 44.14/5.92  fof(f86,plain,(
% 44.14/5.92    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 44.14/5.92    inference(equality_resolution,[],[f68])).
% 44.14/5.92  fof(f68,plain,(
% 44.14/5.92    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 44.14/5.92    inference(cnf_transformation,[],[f41])).
% 44.14/5.93  fof(f41,plain,(
% 44.14/5.93    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((~r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X0)) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 44.14/5.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f39,f40])).
% 44.14/5.93  fof(f40,plain,(
% 44.14/5.93    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((~r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X0)) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 44.14/5.93    introduced(choice_axiom,[])).
% 44.14/5.93  fof(f39,plain,(
% 44.14/5.93    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 44.14/5.93    inference(rectify,[],[f38])).
% 44.14/5.93  fof(f38,plain,(
% 44.14/5.93    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 44.14/5.93    inference(flattening,[],[f37])).
% 44.14/5.93  fof(f37,plain,(
% 44.14/5.93    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 44.14/5.93    inference(nnf_transformation,[],[f4])).
% 44.14/5.93  fof(f4,axiom,(
% 44.14/5.93    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 44.14/5.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 44.14/5.93  fof(f144709,plain,(
% 44.14/5.93    r2_hidden(sK6(sK2,sK0),k1_xboole_0) | ~spl9_149),
% 44.14/5.93    inference(avatar_component_clause,[],[f144707])).
% 44.14/5.93  fof(f144707,plain,(
% 44.14/5.93    spl9_149 <=> r2_hidden(sK6(sK2,sK0),k1_xboole_0)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_149])])).
% 44.14/5.93  fof(f144710,plain,(
% 44.14/5.93    spl9_149 | ~spl9_17 | ~spl9_140 | ~spl9_147),
% 44.14/5.93    inference(avatar_split_clause,[],[f144610,f144304,f135199,f5924,f144707])).
% 44.14/5.93  fof(f5924,plain,(
% 44.14/5.93    spl9_17 <=> ! [X8] : k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X8,sK2))),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 44.14/5.93  fof(f135199,plain,(
% 44.14/5.93    spl9_140 <=> r2_hidden(sK6(sK2,sK0),k3_xboole_0(sK0,k1_tarski(sK6(sK2,sK0))))),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_140])])).
% 44.14/5.93  fof(f144304,plain,(
% 44.14/5.93    spl9_147 <=> k1_tarski(sK6(sK2,sK0)) = k4_xboole_0(k1_tarski(sK6(sK2,sK0)),sK2)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_147])])).
% 44.14/5.93  fof(f144610,plain,(
% 44.14/5.93    r2_hidden(sK6(sK2,sK0),k1_xboole_0) | (~spl9_17 | ~spl9_140 | ~spl9_147)),
% 44.14/5.93    inference(backward_demodulation,[],[f135201,f144529])).
% 44.14/5.93  fof(f144529,plain,(
% 44.14/5.93    k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK6(sK2,sK0))) | (~spl9_17 | ~spl9_147)),
% 44.14/5.93    inference(superposition,[],[f5925,f144306])).
% 44.14/5.93  fof(f144306,plain,(
% 44.14/5.93    k1_tarski(sK6(sK2,sK0)) = k4_xboole_0(k1_tarski(sK6(sK2,sK0)),sK2) | ~spl9_147),
% 44.14/5.93    inference(avatar_component_clause,[],[f144304])).
% 44.14/5.93  fof(f5925,plain,(
% 44.14/5.93    ( ! [X8] : (k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X8,sK2))) ) | ~spl9_17),
% 44.14/5.93    inference(avatar_component_clause,[],[f5924])).
% 44.14/5.93  fof(f135201,plain,(
% 44.14/5.93    r2_hidden(sK6(sK2,sK0),k3_xboole_0(sK0,k1_tarski(sK6(sK2,sK0)))) | ~spl9_140),
% 44.14/5.93    inference(avatar_component_clause,[],[f135199])).
% 44.14/5.93  fof(f144343,plain,(
% 44.14/5.93    spl9_7 | ~spl9_148 | ~spl9_129),
% 44.14/5.93    inference(avatar_split_clause,[],[f129024,f128607,f144340,f174])).
% 44.14/5.93  fof(f174,plain,(
% 44.14/5.93    spl9_7 <=> k1_xboole_0 = sK2),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 44.14/5.93  fof(f144340,plain,(
% 44.14/5.93    spl9_148 <=> r2_hidden(sK6(k1_xboole_0,sK2),k1_tarski(sK6(sK2,sK0)))),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_148])])).
% 44.14/5.93  fof(f128607,plain,(
% 44.14/5.93    spl9_129 <=> sK2 = k4_xboole_0(sK2,k1_tarski(sK6(sK2,sK0)))),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_129])])).
% 44.14/5.93  fof(f129024,plain,(
% 44.14/5.93    ~r2_hidden(sK6(k1_xboole_0,sK2),k1_tarski(sK6(sK2,sK0))) | k1_xboole_0 = sK2 | ~spl9_129),
% 44.14/5.93    inference(superposition,[],[f95608,f128609])).
% 44.14/5.93  fof(f128609,plain,(
% 44.14/5.93    sK2 = k4_xboole_0(sK2,k1_tarski(sK6(sK2,sK0))) | ~spl9_129),
% 44.14/5.93    inference(avatar_component_clause,[],[f128607])).
% 44.14/5.93  fof(f95608,plain,(
% 44.14/5.93    ( ! [X14,X13] : (~r2_hidden(sK6(k1_xboole_0,k4_xboole_0(X14,X13)),X13) | k1_xboole_0 = k4_xboole_0(X14,X13)) )),
% 44.14/5.93    inference(superposition,[],[f152,f95320])).
% 44.14/5.93  fof(f95320,plain,(
% 44.14/5.93    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2) )),
% 44.14/5.93    inference(superposition,[],[f84371,f226])).
% 44.14/5.93  fof(f226,plain,(
% 44.14/5.93    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 44.14/5.93    inference(superposition,[],[f223,f53])).
% 44.14/5.93  fof(f53,plain,(
% 44.14/5.93    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 44.14/5.93    inference(cnf_transformation,[],[f1])).
% 44.14/5.93  fof(f1,axiom,(
% 44.14/5.93    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 44.14/5.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 44.14/5.93  fof(f223,plain,(
% 44.14/5.93    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(k4_xboole_0(X2,X3),X2)) )),
% 44.14/5.93    inference(resolution,[],[f220,f54])).
% 44.14/5.93  fof(f54,plain,(
% 44.14/5.93    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 44.14/5.93    inference(cnf_transformation,[],[f20])).
% 44.14/5.93  fof(f20,plain,(
% 44.14/5.93    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 44.14/5.93    inference(ennf_transformation,[],[f8])).
% 44.14/5.93  fof(f8,axiom,(
% 44.14/5.93    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 44.14/5.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 44.14/5.93  fof(f220,plain,(
% 44.14/5.93    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 44.14/5.93    inference(duplicate_literal_removal,[],[f208])).
% 44.14/5.93  fof(f208,plain,(
% 44.14/5.93    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0) | r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 44.14/5.93    inference(resolution,[],[f134,f57])).
% 44.14/5.93  fof(f57,plain,(
% 44.14/5.93    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 44.14/5.93    inference(cnf_transformation,[],[f28])).
% 44.14/5.93  fof(f28,plain,(
% 44.14/5.93    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 44.14/5.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f27])).
% 44.14/5.93  fof(f27,plain,(
% 44.14/5.93    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 44.14/5.93    introduced(choice_axiom,[])).
% 44.14/5.93  fof(f23,plain,(
% 44.14/5.93    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 44.14/5.93    inference(ennf_transformation,[],[f17])).
% 44.14/5.93  fof(f17,plain,(
% 44.14/5.93    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 44.14/5.93    inference(unused_predicate_definition_removal,[],[f2])).
% 44.14/5.93  fof(f2,axiom,(
% 44.14/5.93    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 44.14/5.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 44.14/5.93  fof(f134,plain,(
% 44.14/5.93    ( ! [X2,X0,X1] : (r2_hidden(sK4(k4_xboole_0(X0,X1),X2),X0) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 44.14/5.93    inference(resolution,[],[f87,f56])).
% 44.14/5.93  fof(f56,plain,(
% 44.14/5.93    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 44.14/5.93    inference(cnf_transformation,[],[f28])).
% 44.14/5.93  fof(f87,plain,(
% 44.14/5.93    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 44.14/5.93    inference(equality_resolution,[],[f67])).
% 44.14/5.93  fof(f67,plain,(
% 44.14/5.93    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 44.14/5.93    inference(cnf_transformation,[],[f41])).
% 44.14/5.93  fof(f84371,plain,(
% 44.14/5.93    ( ! [X2,X3] : (k3_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2))) = X2) )),
% 44.14/5.93    inference(resolution,[],[f84352,f54])).
% 44.14/5.93  fof(f84352,plain,(
% 44.14/5.93    ( ! [X2,X3] : (r1_tarski(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2)))) )),
% 44.14/5.93    inference(duplicate_literal_removal,[],[f84284])).
% 44.14/5.93  fof(f84284,plain,(
% 44.14/5.93    ( ! [X2,X3] : (r1_tarski(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2))) | r1_tarski(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2)))) )),
% 44.14/5.93    inference(resolution,[],[f83321,f122])).
% 44.14/5.93  fof(f122,plain,(
% 44.14/5.93    ( ! [X4,X2,X3] : (~r2_hidden(sK4(X2,X3),k4_xboole_0(X4,X2)) | r1_tarski(X2,X3)) )),
% 44.14/5.93    inference(resolution,[],[f86,f56])).
% 44.14/5.93  fof(f83321,plain,(
% 44.14/5.93    ( ! [X4,X5] : (r2_hidden(sK4(X4,k4_xboole_0(X4,X5)),X5) | r1_tarski(X4,k4_xboole_0(X4,X5))) )),
% 44.14/5.93    inference(duplicate_literal_removal,[],[f83261])).
% 44.14/5.93  fof(f83261,plain,(
% 44.14/5.93    ( ! [X4,X5] : (r2_hidden(sK4(X4,k4_xboole_0(X4,X5)),X5) | r1_tarski(X4,k4_xboole_0(X4,X5)) | r1_tarski(X4,k4_xboole_0(X4,X5))) )),
% 44.14/5.93    inference(resolution,[],[f183,f57])).
% 44.14/5.93  fof(f183,plain,(
% 44.14/5.93    ( ! [X4,X2,X3] : (r2_hidden(sK4(X2,X3),k4_xboole_0(X2,X4)) | r2_hidden(sK4(X2,X3),X4) | r1_tarski(X2,X3)) )),
% 44.14/5.93    inference(resolution,[],[f85,f56])).
% 44.14/5.93  fof(f85,plain,(
% 44.14/5.93    ( ! [X4,X0,X1] : (~r2_hidden(X4,X0) | r2_hidden(X4,X1) | r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 44.14/5.93    inference(equality_resolution,[],[f69])).
% 44.14/5.93  fof(f69,plain,(
% 44.14/5.93    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 44.14/5.93    inference(cnf_transformation,[],[f41])).
% 44.14/5.93  fof(f152,plain,(
% 44.14/5.93    ( ! [X0,X1] : (~r2_hidden(sK6(k1_xboole_0,X0),k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 44.14/5.93    inference(resolution,[],[f151,f86])).
% 44.14/5.93  fof(f151,plain,(
% 44.14/5.93    ( ! [X1] : (r2_hidden(sK6(k1_xboole_0,X1),X1) | k1_xboole_0 = X1) )),
% 44.14/5.93    inference(resolution,[],[f149,f65])).
% 44.14/5.93  fof(f65,plain,(
% 44.14/5.93    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r2_hidden(sK6(X0,X1),X1)) )),
% 44.14/5.93    inference(cnf_transformation,[],[f36])).
% 44.14/5.93  fof(f36,plain,(
% 44.14/5.93    ! [X0,X1] : ((~r2_hidden(sK6(X0,X1),X0) & r2_hidden(sK6(X0,X1),X1)) | ~r2_xboole_0(X0,X1))),
% 44.14/5.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f35])).
% 44.14/5.93  fof(f35,plain,(
% 44.14/5.93    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (~r2_hidden(sK6(X0,X1),X0) & r2_hidden(sK6(X0,X1),X1)))),
% 44.14/5.93    introduced(choice_axiom,[])).
% 44.14/5.93  fof(f24,plain,(
% 44.14/5.93    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 44.14/5.93    inference(ennf_transformation,[],[f7])).
% 44.14/5.93  fof(f7,axiom,(
% 44.14/5.93    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 44.14/5.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).
% 44.14/5.93  fof(f149,plain,(
% 44.14/5.93    ( ! [X1] : (r2_xboole_0(k1_xboole_0,X1) | k1_xboole_0 = X1) )),
% 44.14/5.93    inference(resolution,[],[f55,f124])).
% 44.14/5.93  fof(f124,plain,(
% 44.14/5.93    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 44.14/5.93    inference(resolution,[],[f123,f56])).
% 44.14/5.93  fof(f55,plain,(
% 44.14/5.93    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 44.14/5.93    inference(cnf_transformation,[],[f22])).
% 44.14/5.93  fof(f22,plain,(
% 44.14/5.93    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 44.14/5.93    inference(flattening,[],[f21])).
% 44.14/5.93  fof(f21,plain,(
% 44.14/5.93    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 44.14/5.93    inference(ennf_transformation,[],[f16])).
% 44.14/5.93  fof(f16,plain,(
% 44.14/5.93    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 44.14/5.93    inference(unused_predicate_definition_removal,[],[f5])).
% 44.14/5.93  fof(f5,axiom,(
% 44.14/5.93    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 44.14/5.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 44.14/5.93  fof(f144307,plain,(
% 44.14/5.93    spl9_147 | ~spl9_129),
% 44.14/5.93    inference(avatar_split_clause,[],[f129021,f128607,f144304])).
% 44.14/5.93  fof(f129021,plain,(
% 44.14/5.93    k1_tarski(sK6(sK2,sK0)) = k4_xboole_0(k1_tarski(sK6(sK2,sK0)),sK2) | ~spl9_129),
% 44.14/5.93    inference(superposition,[],[f95320,f128609])).
% 44.14/5.93  fof(f139469,plain,(
% 44.14/5.93    spl9_146 | spl9_143),
% 44.14/5.93    inference(avatar_split_clause,[],[f139314,f139297,f139466])).
% 44.14/5.93  fof(f139466,plain,(
% 44.14/5.93    spl9_146 <=> k1_xboole_0 = k3_xboole_0(k1_tarski(sK6(sK1,sK1)),k1_tarski(sK6(k1_xboole_0,sK1)))),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_146])])).
% 44.14/5.93  fof(f139297,plain,(
% 44.14/5.93    spl9_143 <=> r2_hidden(sK6(k1_xboole_0,sK1),k1_tarski(sK6(sK1,sK1)))),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_143])])).
% 44.14/5.93  fof(f139314,plain,(
% 44.14/5.93    k1_xboole_0 = k3_xboole_0(k1_tarski(sK6(sK1,sK1)),k1_tarski(sK6(k1_xboole_0,sK1))) | spl9_143),
% 44.14/5.93    inference(resolution,[],[f139299,f1331])).
% 44.14/5.93  fof(f1331,plain,(
% 44.14/5.93    ( ! [X0,X1] : (r2_hidden(X1,X0) | k1_xboole_0 = k3_xboole_0(X0,k1_tarski(X1))) )),
% 44.14/5.93    inference(resolution,[],[f1300,f90])).
% 44.14/5.93  fof(f90,plain,(
% 44.14/5.93    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 44.14/5.93    inference(equality_resolution,[],[f73])).
% 44.14/5.93  fof(f73,plain,(
% 44.14/5.93    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 44.14/5.93    inference(cnf_transformation,[],[f46])).
% 44.14/5.93  fof(f46,plain,(
% 44.14/5.93    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X0)) | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 44.14/5.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f44,f45])).
% 44.14/5.93  fof(f45,plain,(
% 44.14/5.93    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X0)) | r2_hidden(sK8(X0,X1,X2),X2))))),
% 44.14/5.93    introduced(choice_axiom,[])).
% 44.14/5.93  fof(f44,plain,(
% 44.14/5.93    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 44.14/5.93    inference(rectify,[],[f43])).
% 44.14/5.93  fof(f43,plain,(
% 44.14/5.93    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 44.14/5.93    inference(flattening,[],[f42])).
% 44.14/5.93  fof(f42,plain,(
% 44.14/5.93    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 44.14/5.93    inference(nnf_transformation,[],[f3])).
% 44.14/5.93  fof(f3,axiom,(
% 44.14/5.93    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 44.14/5.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 44.14/5.93  fof(f1300,plain,(
% 44.14/5.93    ( ! [X12,X13] : (r2_hidden(X12,k3_xboole_0(X13,k1_tarski(X12))) | k1_xboole_0 = k3_xboole_0(X13,k1_tarski(X12))) )),
% 44.14/5.93    inference(superposition,[],[f966,f53])).
% 44.14/5.93  fof(f966,plain,(
% 44.14/5.93    ( ! [X8,X7] : (r2_hidden(X7,k3_xboole_0(k1_tarski(X7),X8)) | k1_xboole_0 = k3_xboole_0(k1_tarski(X7),X8)) )),
% 44.14/5.93    inference(forward_demodulation,[],[f965,f309])).
% 44.14/5.93  fof(f309,plain,(
% 44.14/5.93    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k3_xboole_0(X3,k3_xboole_0(X3,X4))) )),
% 44.14/5.93    inference(superposition,[],[f273,f53])).
% 44.14/5.93  fof(f273,plain,(
% 44.14/5.93    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),X2)) )),
% 44.14/5.93    inference(resolution,[],[f266,f54])).
% 44.14/5.93  fof(f266,plain,(
% 44.14/5.93    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X2)) )),
% 44.14/5.93    inference(superposition,[],[f261,f53])).
% 44.14/5.93  fof(f261,plain,(
% 44.14/5.93    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 44.14/5.93    inference(duplicate_literal_removal,[],[f243])).
% 44.14/5.93  fof(f243,plain,(
% 44.14/5.93    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1) | r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 44.14/5.93    inference(resolution,[],[f136,f57])).
% 44.14/5.93  fof(f136,plain,(
% 44.14/5.93    ( ! [X2,X0,X1] : (r2_hidden(sK4(k3_xboole_0(X0,X1),X2),X1) | r1_tarski(k3_xboole_0(X0,X1),X2)) )),
% 44.14/5.93    inference(resolution,[],[f89,f56])).
% 44.14/5.93  fof(f89,plain,(
% 44.14/5.93    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X1)) )),
% 44.14/5.93    inference(equality_resolution,[],[f74])).
% 44.14/5.93  fof(f74,plain,(
% 44.14/5.93    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 44.14/5.93    inference(cnf_transformation,[],[f46])).
% 44.14/5.93  fof(f965,plain,(
% 44.14/5.93    ( ! [X8,X7] : (r2_hidden(X7,k3_xboole_0(k1_tarski(X7),k3_xboole_0(k1_tarski(X7),X8))) | k1_xboole_0 = k3_xboole_0(k1_tarski(X7),X8)) )),
% 44.14/5.93    inference(forward_demodulation,[],[f961,f53])).
% 44.14/5.93  fof(f961,plain,(
% 44.14/5.93    ( ! [X8,X7] : (r2_hidden(X7,k3_xboole_0(k3_xboole_0(k1_tarski(X7),X8),k1_tarski(X7))) | k1_xboole_0 = k3_xboole_0(k1_tarski(X7),X8)) )),
% 44.14/5.93    inference(duplicate_literal_removal,[],[f956])).
% 44.14/5.93  fof(f956,plain,(
% 44.14/5.93    ( ! [X8,X7] : (r2_hidden(X7,k3_xboole_0(k3_xboole_0(k1_tarski(X7),X8),k1_tarski(X7))) | k1_xboole_0 = k3_xboole_0(k1_tarski(X7),X8) | k1_xboole_0 = k3_xboole_0(k1_tarski(X7),X8)) )),
% 44.14/5.93    inference(superposition,[],[f199,f473])).
% 44.14/5.93  fof(f473,plain,(
% 44.14/5.93    ( ! [X24,X23] : (sK6(k1_xboole_0,k3_xboole_0(k1_tarski(X23),X24)) = X23 | k1_xboole_0 = k3_xboole_0(k1_tarski(X23),X24)) )),
% 44.14/5.93    inference(resolution,[],[f153,f82])).
% 44.14/5.93  fof(f82,plain,(
% 44.14/5.93    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 44.14/5.93    inference(equality_resolution,[],[f58])).
% 44.14/5.93  fof(f58,plain,(
% 44.14/5.93    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 44.14/5.93    inference(cnf_transformation,[],[f32])).
% 44.14/5.93  fof(f153,plain,(
% 44.14/5.93    ( ! [X2,X3] : (r2_hidden(sK6(k1_xboole_0,k3_xboole_0(X2,X3)),X2) | k1_xboole_0 = k3_xboole_0(X2,X3)) )),
% 44.14/5.93    inference(resolution,[],[f151,f90])).
% 44.14/5.93  fof(f199,plain,(
% 44.14/5.93    ( ! [X5] : (r2_hidden(sK6(k1_xboole_0,X5),k3_xboole_0(X5,k1_tarski(sK6(k1_xboole_0,X5)))) | k1_xboole_0 = X5) )),
% 44.14/5.93    inference(resolution,[],[f192,f151])).
% 44.14/5.93  fof(f192,plain,(
% 44.14/5.93    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(X0,k3_xboole_0(X1,k1_tarski(X0)))) )),
% 44.14/5.93    inference(resolution,[],[f88,f81])).
% 44.14/5.93  fof(f88,plain,(
% 44.14/5.93    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 44.14/5.93    inference(equality_resolution,[],[f75])).
% 44.14/5.93  fof(f75,plain,(
% 44.14/5.93    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 44.14/5.93    inference(cnf_transformation,[],[f46])).
% 44.14/5.93  fof(f139299,plain,(
% 44.14/5.93    ~r2_hidden(sK6(k1_xboole_0,sK1),k1_tarski(sK6(sK1,sK1))) | spl9_143),
% 44.14/5.93    inference(avatar_component_clause,[],[f139297])).
% 44.14/5.93  fof(f139464,plain,(
% 44.14/5.93    spl9_145 | spl9_143),
% 44.14/5.93    inference(avatar_split_clause,[],[f139301,f139297,f139461])).
% 44.14/5.93  fof(f139461,plain,(
% 44.14/5.93    spl9_145 <=> k1_xboole_0 = k3_xboole_0(k1_tarski(sK6(k1_xboole_0,sK1)),k1_tarski(sK6(sK1,sK1)))),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_145])])).
% 44.14/5.93  fof(f139301,plain,(
% 44.14/5.93    k1_xboole_0 = k3_xboole_0(k1_tarski(sK6(k1_xboole_0,sK1)),k1_tarski(sK6(sK1,sK1))) | spl9_143),
% 44.14/5.93    inference(resolution,[],[f139299,f963])).
% 44.14/5.93  fof(f963,plain,(
% 44.14/5.93    ( ! [X4,X3] : (r2_hidden(X3,X4) | k1_xboole_0 = k3_xboole_0(k1_tarski(X3),X4)) )),
% 44.14/5.93    inference(duplicate_literal_removal,[],[f954])).
% 44.14/5.93  fof(f954,plain,(
% 44.14/5.93    ( ! [X4,X3] : (r2_hidden(X3,X4) | k1_xboole_0 = k3_xboole_0(k1_tarski(X3),X4) | k1_xboole_0 = k3_xboole_0(k1_tarski(X3),X4)) )),
% 44.14/5.93    inference(superposition,[],[f154,f473])).
% 44.14/5.93  fof(f154,plain,(
% 44.14/5.93    ( ! [X4,X5] : (r2_hidden(sK6(k1_xboole_0,k3_xboole_0(X4,X5)),X5) | k1_xboole_0 = k3_xboole_0(X4,X5)) )),
% 44.14/5.93    inference(resolution,[],[f151,f89])).
% 44.14/5.93  fof(f139431,plain,(
% 44.14/5.93    ~spl9_144 | ~spl9_97 | ~spl9_142),
% 44.14/5.93    inference(avatar_split_clause,[],[f139344,f139261,f96470,f139428])).
% 44.14/5.93  fof(f139428,plain,(
% 44.14/5.93    spl9_144 <=> r2_hidden(sK4(sK1,k1_xboole_0),k1_tarski(sK6(sK1,sK1)))),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_144])])).
% 44.14/5.93  fof(f96470,plain,(
% 44.14/5.93    spl9_97 <=> r2_hidden(sK4(sK1,k1_xboole_0),sK1)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_97])])).
% 44.14/5.93  fof(f139261,plain,(
% 44.14/5.93    spl9_142 <=> k1_tarski(sK6(sK1,sK1)) = k4_xboole_0(k1_tarski(sK6(sK1,sK1)),sK1)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_142])])).
% 44.14/5.93  fof(f139344,plain,(
% 44.14/5.93    ~r2_hidden(sK4(sK1,k1_xboole_0),k1_tarski(sK6(sK1,sK1))) | (~spl9_97 | ~spl9_142)),
% 44.14/5.93    inference(superposition,[],[f96475,f139263])).
% 44.14/5.93  fof(f139263,plain,(
% 44.14/5.93    k1_tarski(sK6(sK1,sK1)) = k4_xboole_0(k1_tarski(sK6(sK1,sK1)),sK1) | ~spl9_142),
% 44.14/5.93    inference(avatar_component_clause,[],[f139261])).
% 44.14/5.93  fof(f96475,plain,(
% 44.14/5.93    ( ! [X1] : (~r2_hidden(sK4(sK1,k1_xboole_0),k4_xboole_0(X1,sK1))) ) | ~spl9_97),
% 44.14/5.93    inference(resolution,[],[f96472,f86])).
% 44.14/5.93  fof(f96472,plain,(
% 44.14/5.93    r2_hidden(sK4(sK1,k1_xboole_0),sK1) | ~spl9_97),
% 44.14/5.93    inference(avatar_component_clause,[],[f96470])).
% 44.14/5.93  fof(f139300,plain,(
% 44.14/5.93    spl9_2 | ~spl9_143 | ~spl9_133),
% 44.14/5.93    inference(avatar_split_clause,[],[f129587,f129483,f139297,f98])).
% 44.14/5.93  fof(f98,plain,(
% 44.14/5.93    spl9_2 <=> k1_xboole_0 = sK1),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 44.14/5.93  fof(f129483,plain,(
% 44.14/5.93    spl9_133 <=> sK1 = k4_xboole_0(sK1,k1_tarski(sK6(sK1,sK1)))),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_133])])).
% 44.14/5.93  fof(f129587,plain,(
% 44.14/5.93    ~r2_hidden(sK6(k1_xboole_0,sK1),k1_tarski(sK6(sK1,sK1))) | k1_xboole_0 = sK1 | ~spl9_133),
% 44.14/5.93    inference(superposition,[],[f95608,f129485])).
% 44.14/5.93  fof(f129485,plain,(
% 44.14/5.93    sK1 = k4_xboole_0(sK1,k1_tarski(sK6(sK1,sK1))) | ~spl9_133),
% 44.14/5.93    inference(avatar_component_clause,[],[f129483])).
% 44.14/5.93  fof(f139264,plain,(
% 44.14/5.93    spl9_142 | ~spl9_133),
% 44.14/5.93    inference(avatar_split_clause,[],[f129584,f129483,f139261])).
% 44.14/5.93  fof(f129584,plain,(
% 44.14/5.93    k1_tarski(sK6(sK1,sK1)) = k4_xboole_0(k1_tarski(sK6(sK1,sK1)),sK1) | ~spl9_133),
% 44.14/5.93    inference(superposition,[],[f95320,f129485])).
% 44.14/5.93  fof(f136503,plain,(
% 44.14/5.93    spl9_141 | ~spl9_124),
% 44.14/5.93    inference(avatar_split_clause,[],[f126956,f126947,f136500])).
% 44.14/5.93  fof(f136500,plain,(
% 44.14/5.93    spl9_141 <=> r2_hidden(sK4(sK0,k1_xboole_0),k3_xboole_0(sK0,k1_tarski(sK4(sK0,k1_xboole_0))))),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_141])])).
% 44.14/5.93  fof(f126947,plain,(
% 44.14/5.93    spl9_124 <=> r2_hidden(sK4(sK0,k1_xboole_0),sK0)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_124])])).
% 44.14/5.93  fof(f126956,plain,(
% 44.14/5.93    r2_hidden(sK4(sK0,k1_xboole_0),k3_xboole_0(sK0,k1_tarski(sK4(sK0,k1_xboole_0)))) | ~spl9_124),
% 44.14/5.93    inference(resolution,[],[f126949,f192])).
% 44.14/5.93  fof(f126949,plain,(
% 44.14/5.93    r2_hidden(sK4(sK0,k1_xboole_0),sK0) | ~spl9_124),
% 44.14/5.93    inference(avatar_component_clause,[],[f126947])).
% 44.14/5.93  fof(f135202,plain,(
% 44.14/5.93    spl9_140 | ~spl9_77),
% 44.14/5.93    inference(avatar_split_clause,[],[f119015,f81302,f135199])).
% 44.14/5.93  fof(f81302,plain,(
% 44.14/5.93    spl9_77 <=> r2_hidden(sK6(sK2,sK0),sK0)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_77])])).
% 44.14/5.93  fof(f119015,plain,(
% 44.14/5.93    r2_hidden(sK6(sK2,sK0),k3_xboole_0(sK0,k1_tarski(sK6(sK2,sK0)))) | ~spl9_77),
% 44.14/5.93    inference(forward_demodulation,[],[f81341,f84413])).
% 44.14/5.93  fof(f84413,plain,(
% 44.14/5.93    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = X1) )),
% 44.14/5.93    inference(superposition,[],[f84358,f226])).
% 44.14/5.93  fof(f84358,plain,(
% 44.14/5.93    ( ! [X1] : (k3_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = X1) )),
% 44.14/5.93    inference(resolution,[],[f84309,f54])).
% 44.14/5.93  fof(f84309,plain,(
% 44.14/5.93    ( ! [X76] : (r1_tarski(X76,k4_xboole_0(X76,k1_xboole_0))) )),
% 44.14/5.93    inference(resolution,[],[f83321,f123])).
% 44.14/5.93  fof(f81341,plain,(
% 44.14/5.93    r2_hidden(sK6(sK2,sK0),k3_xboole_0(sK0,k4_xboole_0(k1_tarski(sK6(sK2,sK0)),k1_xboole_0))) | ~spl9_77),
% 44.14/5.93    inference(resolution,[],[f81304,f2127])).
% 44.14/5.93  fof(f2127,plain,(
% 44.14/5.93    ( ! [X8,X9] : (~r2_hidden(X8,X9) | r2_hidden(X8,k3_xboole_0(X9,k4_xboole_0(k1_tarski(X8),k1_xboole_0)))) )),
% 44.14/5.93    inference(resolution,[],[f2026,f88])).
% 44.14/5.93  fof(f2026,plain,(
% 44.14/5.93    ( ! [X0] : (r2_hidden(X0,k4_xboole_0(k1_tarski(X0),k1_xboole_0))) )),
% 44.14/5.93    inference(superposition,[],[f2014,f51])).
% 44.14/5.93  fof(f2014,plain,(
% 44.14/5.93    ( ! [X0,X1] : (r2_hidden(X0,k4_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0))))) )),
% 44.14/5.93    inference(global_subsumption,[],[f123,f1984])).
% 44.14/5.93  fof(f1984,plain,(
% 44.14/5.93    ( ! [X0,X1] : (r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,k4_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0))))) )),
% 44.14/5.93    inference(superposition,[],[f182,f1896])).
% 44.14/5.93  fof(f1896,plain,(
% 44.14/5.93    ( ! [X24,X25] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X24),k4_xboole_0(k1_tarski(X24),k4_xboole_0(X25,k1_tarski(X24))))) )),
% 44.14/5.93    inference(resolution,[],[f1629,f121])).
% 44.14/5.93  fof(f1629,plain,(
% 44.14/5.93    ( ! [X8,X7] : (r2_hidden(X7,X8) | k1_xboole_0 = k4_xboole_0(k1_tarski(X7),k4_xboole_0(k1_tarski(X7),X8))) )),
% 44.14/5.93    inference(resolution,[],[f1304,f188])).
% 44.14/5.93  fof(f188,plain,(
% 44.14/5.93    ( ! [X6,X8,X7] : (~r2_hidden(X6,k4_xboole_0(X8,k4_xboole_0(k1_tarski(X6),X7))) | r2_hidden(X6,X7)) )),
% 44.14/5.93    inference(resolution,[],[f182,f86])).
% 44.14/5.93  fof(f1304,plain,(
% 44.14/5.93    ( ! [X21,X20] : (r2_hidden(X20,k4_xboole_0(k1_tarski(X20),X21)) | k1_xboole_0 = k4_xboole_0(k1_tarski(X20),X21)) )),
% 44.14/5.93    inference(superposition,[],[f966,f226])).
% 44.14/5.93  fof(f182,plain,(
% 44.14/5.93    ( ! [X0,X1] : (r2_hidden(X0,k4_xboole_0(k1_tarski(X0),X1)) | r2_hidden(X0,X1)) )),
% 44.14/5.93    inference(resolution,[],[f85,f81])).
% 44.14/5.93  fof(f81304,plain,(
% 44.14/5.93    r2_hidden(sK6(sK2,sK0),sK0) | ~spl9_77),
% 44.14/5.93    inference(avatar_component_clause,[],[f81302])).
% 44.14/5.93  fof(f134281,plain,(
% 44.14/5.93    spl9_139 | ~spl9_78),
% 44.14/5.93    inference(avatar_split_clause,[],[f119013,f81578,f134278])).
% 44.14/5.93  fof(f134278,plain,(
% 44.14/5.93    spl9_139 <=> r2_hidden(sK6(k1_xboole_0,sK2),k3_xboole_0(sK0,k1_tarski(sK6(k1_xboole_0,sK2))))),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_139])])).
% 44.14/5.93  fof(f81578,plain,(
% 44.14/5.93    spl9_78 <=> r2_hidden(sK6(k1_xboole_0,sK2),sK0)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_78])])).
% 44.14/5.93  fof(f119013,plain,(
% 44.14/5.93    r2_hidden(sK6(k1_xboole_0,sK2),k3_xboole_0(sK0,k1_tarski(sK6(k1_xboole_0,sK2)))) | ~spl9_78),
% 44.14/5.93    inference(forward_demodulation,[],[f81589,f84413])).
% 44.14/5.93  fof(f81589,plain,(
% 44.14/5.93    r2_hidden(sK6(k1_xboole_0,sK2),k3_xboole_0(sK0,k4_xboole_0(k1_tarski(sK6(k1_xboole_0,sK2)),k1_xboole_0))) | ~spl9_78),
% 44.14/5.93    inference(resolution,[],[f81580,f2127])).
% 44.14/5.93  fof(f81580,plain,(
% 44.14/5.93    r2_hidden(sK6(k1_xboole_0,sK2),sK0) | ~spl9_78),
% 44.14/5.93    inference(avatar_component_clause,[],[f81578])).
% 44.14/5.93  fof(f131409,plain,(
% 44.14/5.93    spl9_138 | ~spl9_123),
% 44.14/5.93    inference(avatar_split_clause,[],[f126559,f122817,f131406])).
% 44.14/5.93  fof(f131406,plain,(
% 44.14/5.93    spl9_138 <=> r2_hidden(sK4(sK0,k1_xboole_0),k3_xboole_0(sK2,k1_tarski(sK4(sK0,k1_xboole_0))))),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_138])])).
% 44.14/5.93  fof(f122817,plain,(
% 44.14/5.93    spl9_123 <=> r2_hidden(sK4(sK0,k1_xboole_0),sK2)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_123])])).
% 44.14/5.93  fof(f126559,plain,(
% 44.14/5.93    r2_hidden(sK4(sK0,k1_xboole_0),k3_xboole_0(sK2,k1_tarski(sK4(sK0,k1_xboole_0)))) | ~spl9_123),
% 44.14/5.93    inference(resolution,[],[f122819,f192])).
% 44.14/5.93  fof(f122819,plain,(
% 44.14/5.93    r2_hidden(sK4(sK0,k1_xboole_0),sK2) | ~spl9_123),
% 44.14/5.93    inference(avatar_component_clause,[],[f122817])).
% 44.14/5.93  fof(f129824,plain,(
% 44.14/5.93    spl9_7 | spl9_137 | ~spl9_73),
% 44.14/5.93    inference(avatar_split_clause,[],[f80977,f78248,f129822,f174])).
% 44.14/5.93  fof(f129822,plain,(
% 44.14/5.93    spl9_137 <=> ! [X111] : r2_hidden(sK8(X111,k1_xboole_0,sK2),sK0)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_137])])).
% 44.14/5.93  fof(f78248,plain,(
% 44.14/5.93    spl9_73 <=> sK2 = k3_xboole_0(sK0,sK2)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_73])])).
% 44.14/5.93  fof(f80977,plain,(
% 44.14/5.93    ( ! [X111] : (r2_hidden(sK8(X111,k1_xboole_0,sK2),sK0) | k1_xboole_0 = sK2) ) | ~spl9_73),
% 44.14/5.93    inference(superposition,[],[f41943,f78250])).
% 44.14/5.93  fof(f78250,plain,(
% 44.14/5.93    sK2 = k3_xboole_0(sK0,sK2) | ~spl9_73),
% 44.14/5.93    inference(avatar_component_clause,[],[f78248])).
% 44.14/5.93  fof(f41943,plain,(
% 44.14/5.93    ( ! [X24,X23,X22] : (r2_hidden(sK8(X24,k1_xboole_0,k3_xboole_0(X22,X23)),X22) | k1_xboole_0 = k3_xboole_0(X22,X23)) )),
% 44.14/5.93    inference(resolution,[],[f41931,f90])).
% 44.14/5.93  fof(f41931,plain,(
% 44.14/5.93    ( ! [X90,X91] : (r2_hidden(sK8(X90,k1_xboole_0,X91),X91) | k1_xboole_0 = X91) )),
% 44.14/5.93    inference(forward_demodulation,[],[f41871,f126])).
% 44.14/5.93  fof(f126,plain,(
% 44.14/5.93    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 44.14/5.93    inference(superposition,[],[f125,f53])).
% 44.14/5.93  fof(f125,plain,(
% 44.14/5.93    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 44.14/5.93    inference(resolution,[],[f124,f54])).
% 44.14/5.93  fof(f41871,plain,(
% 44.14/5.93    ( ! [X90,X91] : (r2_hidden(sK8(X90,k1_xboole_0,X91),X91) | k3_xboole_0(X90,k1_xboole_0) = X91) )),
% 44.14/5.93    inference(resolution,[],[f77,f123])).
% 44.14/5.93  fof(f77,plain,(
% 44.14/5.93    ( ! [X2,X0,X1] : (r2_hidden(sK8(X0,X1,X2),X1) | r2_hidden(sK8(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 44.14/5.93    inference(cnf_transformation,[],[f46])).
% 44.14/5.93  fof(f129755,plain,(
% 44.14/5.93    spl9_7 | spl9_136 | ~spl9_73),
% 44.14/5.93    inference(avatar_split_clause,[],[f80973,f78248,f129753,f174])).
% 44.14/5.93  fof(f129753,plain,(
% 44.14/5.93    spl9_136 <=> ! [X107] : r2_hidden(sK8(k1_xboole_0,X107,sK2),sK0)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_136])])).
% 44.14/5.93  fof(f80973,plain,(
% 44.14/5.93    ( ! [X107] : (r2_hidden(sK8(k1_xboole_0,X107,sK2),sK0) | k1_xboole_0 = sK2) ) | ~spl9_73),
% 44.14/5.93    inference(superposition,[],[f21863,f78250])).
% 44.14/5.93  fof(f21863,plain,(
% 44.14/5.93    ( ! [X21,X22,X20] : (r2_hidden(sK8(k1_xboole_0,X22,k3_xboole_0(X20,X21)),X20) | k1_xboole_0 = k3_xboole_0(X20,X21)) )),
% 44.14/5.93    inference(resolution,[],[f21852,f90])).
% 44.14/5.93  fof(f21852,plain,(
% 44.14/5.93    ( ! [X52,X51] : (r2_hidden(sK8(k1_xboole_0,X51,X52),X52) | k1_xboole_0 = X52) )),
% 44.14/5.93    inference(forward_demodulation,[],[f21807,f125])).
% 44.14/5.93  fof(f21807,plain,(
% 44.14/5.93    ( ! [X52,X51] : (r2_hidden(sK8(k1_xboole_0,X51,X52),X52) | k3_xboole_0(k1_xboole_0,X51) = X52) )),
% 44.14/5.93    inference(resolution,[],[f76,f123])).
% 44.14/5.93  fof(f76,plain,(
% 44.14/5.93    ( ! [X2,X0,X1] : (r2_hidden(sK8(X0,X1,X2),X0) | r2_hidden(sK8(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 44.14/5.93    inference(cnf_transformation,[],[f46])).
% 44.14/5.93  fof(f129684,plain,(
% 44.14/5.93    spl9_7 | spl9_135 | ~spl9_73),
% 44.14/5.93    inference(avatar_split_clause,[],[f80949,f78248,f129682,f174])).
% 44.14/5.93  fof(f129682,plain,(
% 44.14/5.93    spl9_135 <=> ! [X59] : r2_hidden(sK7(X59,X59,sK2),sK0)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_135])])).
% 44.14/5.93  fof(f80949,plain,(
% 44.14/5.93    ( ! [X59] : (r2_hidden(sK7(X59,X59,sK2),sK0) | k1_xboole_0 = sK2) ) | ~spl9_73),
% 44.14/5.93    inference(superposition,[],[f11528,f78250])).
% 44.14/5.93  fof(f11528,plain,(
% 44.14/5.93    ( ! [X23,X21,X22] : (r2_hidden(sK7(X23,X23,k3_xboole_0(X21,X22)),X21) | k1_xboole_0 = k3_xboole_0(X21,X22)) )),
% 44.14/5.93    inference(resolution,[],[f11517,f90])).
% 44.14/5.93  fof(f11517,plain,(
% 44.14/5.93    ( ! [X0,X1] : (r2_hidden(sK7(X0,X0,X1),X1) | k1_xboole_0 = X1) )),
% 44.14/5.93    inference(forward_demodulation,[],[f11516,f608])).
% 44.14/5.93  fof(f608,plain,(
% 44.14/5.93    ( ! [X14] : (k1_xboole_0 = k4_xboole_0(X14,X14)) )),
% 44.14/5.93    inference(superposition,[],[f600,f126])).
% 44.14/5.93  fof(f600,plain,(
% 44.14/5.93    ( ! [X2,X3] : (k4_xboole_0(X2,X2) = k3_xboole_0(k4_xboole_0(X2,X2),X3)) )),
% 44.14/5.93    inference(resolution,[],[f598,f54])).
% 44.14/5.93  fof(f598,plain,(
% 44.14/5.93    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),X1)) )),
% 44.14/5.93    inference(duplicate_literal_removal,[],[f592])).
% 44.14/5.93  fof(f592,plain,(
% 44.14/5.93    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),X1) | r1_tarski(k4_xboole_0(X0,X0),X1)) )),
% 44.14/5.93    inference(resolution,[],[f213,f56])).
% 44.14/5.93  fof(f213,plain,(
% 44.14/5.93    ( ! [X19,X17,X18,X16] : (~r2_hidden(sK4(k4_xboole_0(X16,X17),X18),k4_xboole_0(X19,X16)) | r1_tarski(k4_xboole_0(X16,X17),X18)) )),
% 44.14/5.93    inference(resolution,[],[f134,f86])).
% 44.14/5.93  fof(f11516,plain,(
% 44.14/5.93    ( ! [X0,X1] : (k4_xboole_0(X0,X0) = X1 | r2_hidden(sK7(X0,X0,X1),X1)) )),
% 44.14/5.93    inference(duplicate_literal_removal,[],[f11498])).
% 44.14/5.93  fof(f11498,plain,(
% 44.14/5.93    ( ! [X0,X1] : (k4_xboole_0(X0,X0) = X1 | r2_hidden(sK7(X0,X0,X1),X1) | r2_hidden(sK7(X0,X0,X1),X1) | k4_xboole_0(X0,X0) = X1) )),
% 44.14/5.93    inference(resolution,[],[f71,f70])).
% 44.14/5.93  fof(f70,plain,(
% 44.14/5.93    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 44.14/5.93    inference(cnf_transformation,[],[f41])).
% 44.14/5.93  fof(f71,plain,(
% 44.14/5.93    ( ! [X2,X0,X1] : (~r2_hidden(sK7(X0,X1,X2),X1) | k4_xboole_0(X0,X1) = X2 | r2_hidden(sK7(X0,X1,X2),X2)) )),
% 44.14/5.93    inference(cnf_transformation,[],[f41])).
% 44.14/5.93  fof(f129616,plain,(
% 44.14/5.93    spl9_7 | spl9_134 | ~spl9_73),
% 44.14/5.93    inference(avatar_split_clause,[],[f80947,f78248,f129614,f174])).
% 44.14/5.93  fof(f129614,plain,(
% 44.14/5.93    spl9_134 <=> ! [X57] : r2_hidden(sK7(k1_xboole_0,X57,sK2),sK0)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_134])])).
% 44.14/5.93  fof(f80947,plain,(
% 44.14/5.93    ( ! [X57] : (r2_hidden(sK7(k1_xboole_0,X57,sK2),sK0) | k1_xboole_0 = sK2) ) | ~spl9_73),
% 44.14/5.93    inference(superposition,[],[f6903,f78250])).
% 44.14/5.93  fof(f6903,plain,(
% 44.14/5.93    ( ! [X21,X22,X20] : (r2_hidden(sK7(k1_xboole_0,X22,k3_xboole_0(X20,X21)),X20) | k1_xboole_0 = k3_xboole_0(X20,X21)) )),
% 44.14/5.93    inference(resolution,[],[f6848,f90])).
% 44.14/5.93  fof(f6848,plain,(
% 44.14/5.93    ( ! [X52,X51] : (r2_hidden(sK7(k1_xboole_0,X51,X52),X52) | k1_xboole_0 = X52) )),
% 44.14/5.93    inference(forward_demodulation,[],[f6809,f51])).
% 44.14/5.93  fof(f6809,plain,(
% 44.14/5.93    ( ! [X52,X51] : (r2_hidden(sK7(k1_xboole_0,X51,X52),X52) | k4_xboole_0(k1_xboole_0,X51) = X52) )),
% 44.14/5.93    inference(resolution,[],[f70,f123])).
% 44.14/5.93  fof(f129486,plain,(
% 44.14/5.93    spl9_133 | spl9_121),
% 44.14/5.93    inference(avatar_split_clause,[],[f129078,f121979,f129483])).
% 44.14/5.93  fof(f121979,plain,(
% 44.14/5.93    spl9_121 <=> r2_hidden(sK6(sK1,sK1),sK1)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_121])])).
% 44.14/5.93  fof(f129078,plain,(
% 44.14/5.93    sK1 = k4_xboole_0(sK1,k1_tarski(sK6(sK1,sK1))) | spl9_121),
% 44.14/5.93    inference(resolution,[],[f121980,f111163])).
% 44.14/5.93  fof(f111163,plain,(
% 44.14/5.93    ( ! [X4,X3] : (r2_hidden(X3,X4) | k4_xboole_0(X4,k1_tarski(X3)) = X4) )),
% 44.14/5.93    inference(global_subsumption,[],[f123,f110963])).
% 44.14/5.93  fof(f110963,plain,(
% 44.14/5.93    ( ! [X4,X3] : (r2_hidden(X3,k1_xboole_0) | r2_hidden(X3,X4) | k4_xboole_0(X4,k1_tarski(X3)) = X4) )),
% 44.14/5.93    inference(superposition,[],[f182,f95580])).
% 44.14/5.93  fof(f95580,plain,(
% 44.14/5.93    ( ! [X6,X5] : (k4_xboole_0(X6,k1_tarski(X5)) = X6 | k1_xboole_0 = k4_xboole_0(k1_tarski(X5),X6)) )),
% 44.14/5.93    inference(superposition,[],[f95320,f41576])).
% 44.14/5.93  fof(f41576,plain,(
% 44.14/5.93    ( ! [X74,X73] : (k1_tarski(X73) = k4_xboole_0(k1_tarski(X73),X74) | k1_xboole_0 = k4_xboole_0(k1_tarski(X73),X74)) )),
% 44.14/5.93    inference(superposition,[],[f39742,f226])).
% 44.14/5.93  fof(f39742,plain,(
% 44.14/5.93    ( ! [X6,X5] : (k1_tarski(X6) = k3_xboole_0(k1_tarski(X6),X5) | k1_xboole_0 = k3_xboole_0(k1_tarski(X6),X5)) )),
% 44.14/5.93    inference(superposition,[],[f36640,f53])).
% 44.14/5.93  fof(f36640,plain,(
% 44.14/5.93    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_tarski(X0)) | k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)) )),
% 44.14/5.93    inference(duplicate_literal_removal,[],[f36461])).
% 44.14/5.93  fof(f36461,plain,(
% 44.14/5.93    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_tarski(X0)) | k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)) )),
% 44.14/5.93    inference(superposition,[],[f1141,f159])).
% 44.14/5.93  fof(f159,plain,(
% 44.14/5.93    ( ! [X2,X3] : (sK4(k1_tarski(X2),X3) = X2 | k1_tarski(X2) = k3_xboole_0(k1_tarski(X2),X3)) )),
% 44.14/5.93    inference(resolution,[],[f117,f54])).
% 44.14/5.93  fof(f117,plain,(
% 44.14/5.93    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | sK4(k1_tarski(X0),X1) = X0) )),
% 44.14/5.93    inference(resolution,[],[f56,f82])).
% 44.14/5.93  fof(f1141,plain,(
% 44.14/5.93    ( ! [X2,X3] : (k1_xboole_0 = k3_xboole_0(X2,k1_tarski(sK4(X3,X2))) | k3_xboole_0(X3,X2) = X3) )),
% 44.14/5.93    inference(resolution,[],[f994,f54])).
% 44.14/5.93  fof(f994,plain,(
% 44.14/5.93    ( ! [X35,X36] : (r1_tarski(X35,X36) | k1_xboole_0 = k3_xboole_0(X36,k1_tarski(sK4(X35,X36)))) )),
% 44.14/5.93    inference(forward_demodulation,[],[f981,f53])).
% 44.14/5.93  fof(f981,plain,(
% 44.14/5.93    ( ! [X35,X36] : (k1_xboole_0 = k3_xboole_0(k1_tarski(sK4(X35,X36)),X36) | r1_tarski(X35,X36)) )),
% 44.14/5.93    inference(resolution,[],[f963,f57])).
% 44.14/5.93  fof(f121980,plain,(
% 44.14/5.93    ~r2_hidden(sK6(sK1,sK1),sK1) | spl9_121),
% 44.14/5.93    inference(avatar_component_clause,[],[f121979])).
% 44.14/5.93  fof(f129088,plain,(
% 44.14/5.93    spl9_132 | spl9_121),
% 44.14/5.93    inference(avatar_split_clause,[],[f129064,f121979,f129085])).
% 44.14/5.93  fof(f129085,plain,(
% 44.14/5.93    spl9_132 <=> k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK6(sK1,sK1)))),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_132])])).
% 44.14/5.93  fof(f129064,plain,(
% 44.14/5.93    k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK6(sK1,sK1))) | spl9_121),
% 44.14/5.93    inference(resolution,[],[f121980,f1331])).
% 44.14/5.93  fof(f129083,plain,(
% 44.14/5.93    spl9_131 | spl9_121),
% 44.14/5.93    inference(avatar_split_clause,[],[f129051,f121979,f129080])).
% 44.14/5.93  fof(f129080,plain,(
% 44.14/5.93    spl9_131 <=> k1_xboole_0 = k3_xboole_0(k1_tarski(sK6(sK1,sK1)),sK1)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_131])])).
% 44.14/5.93  fof(f129051,plain,(
% 44.14/5.93    k1_xboole_0 = k3_xboole_0(k1_tarski(sK6(sK1,sK1)),sK1) | spl9_121),
% 44.14/5.93    inference(resolution,[],[f121980,f963])).
% 44.14/5.93  fof(f129050,plain,(
% 44.14/5.93    ~spl9_121 | ~spl9_4 | spl9_118),
% 44.14/5.93    inference(avatar_split_clause,[],[f129048,f117410,f107,f121979])).
% 44.14/5.93  fof(f107,plain,(
% 44.14/5.93    spl9_4 <=> sK1 = sK3),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 44.14/5.93  fof(f117410,plain,(
% 44.14/5.93    spl9_118 <=> r2_hidden(sK6(sK3,sK1),sK1)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_118])])).
% 44.14/5.93  fof(f129048,plain,(
% 44.14/5.93    ~r2_hidden(sK6(sK1,sK1),sK1) | (~spl9_4 | spl9_118)),
% 44.14/5.93    inference(forward_demodulation,[],[f117411,f108])).
% 44.14/5.93  fof(f108,plain,(
% 44.14/5.93    sK1 = sK3 | ~spl9_4),
% 44.14/5.93    inference(avatar_component_clause,[],[f107])).
% 44.14/5.93  fof(f117411,plain,(
% 44.14/5.93    ~r2_hidden(sK6(sK3,sK1),sK1) | spl9_118),
% 44.14/5.93    inference(avatar_component_clause,[],[f117410])).
% 44.14/5.93  fof(f129047,plain,(
% 44.14/5.93    spl9_130 | ~spl9_4 | ~spl9_118),
% 44.14/5.93    inference(avatar_split_clause,[],[f120776,f117410,f107,f129044])).
% 44.14/5.93  fof(f129044,plain,(
% 44.14/5.93    spl9_130 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(sK1,sK1)),sK1)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_130])])).
% 44.14/5.93  fof(f120776,plain,(
% 44.14/5.93    k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(sK1,sK1)),sK1) | (~spl9_4 | ~spl9_118)),
% 44.14/5.93    inference(backward_demodulation,[],[f118008,f108])).
% 44.14/5.93  fof(f118008,plain,(
% 44.14/5.93    k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(sK3,sK1)),sK1) | ~spl9_118),
% 44.14/5.93    inference(resolution,[],[f117412,f26029])).
% 44.14/5.93  fof(f26029,plain,(
% 44.14/5.93    ( ! [X6,X5] : (~r2_hidden(X5,X6) | k1_xboole_0 = k4_xboole_0(k1_tarski(X5),X6)) )),
% 44.14/5.93    inference(global_subsumption,[],[f123,f26026])).
% 44.14/5.93  fof(f26026,plain,(
% 44.14/5.93    ( ! [X6,X5] : (~r2_hidden(X5,X6) | k1_xboole_0 = k4_xboole_0(k1_tarski(X5),X6) | r2_hidden(X5,k1_xboole_0)) )),
% 44.14/5.93    inference(duplicate_literal_removal,[],[f26018])).
% 44.14/5.93  fof(f26018,plain,(
% 44.14/5.93    ( ! [X6,X5] : (~r2_hidden(X5,X6) | k1_xboole_0 = k4_xboole_0(k1_tarski(X5),X6) | r2_hidden(X5,k1_xboole_0) | k1_xboole_0 = k4_xboole_0(k1_tarski(X5),X6)) )),
% 44.14/5.93    inference(superposition,[],[f71,f7348])).
% 44.14/5.93  fof(f7348,plain,(
% 44.14/5.93    ( ! [X39,X38] : (sK7(k1_tarski(X38),X39,k1_xboole_0) = X38 | k1_xboole_0 = k4_xboole_0(k1_tarski(X38),X39)) )),
% 44.14/5.93    inference(resolution,[],[f6834,f82])).
% 44.14/5.93  fof(f6834,plain,(
% 44.14/5.93    ( ! [X52,X51] : (r2_hidden(sK7(X51,X52,k1_xboole_0),X51) | k1_xboole_0 = k4_xboole_0(X51,X52)) )),
% 44.14/5.93    inference(resolution,[],[f70,f123])).
% 44.14/5.93  fof(f117412,plain,(
% 44.14/5.93    r2_hidden(sK6(sK3,sK1),sK1) | ~spl9_118),
% 44.14/5.93    inference(avatar_component_clause,[],[f117410])).
% 44.14/5.93  fof(f128610,plain,(
% 44.14/5.93    spl9_129 | spl9_76),
% 44.14/5.93    inference(avatar_split_clause,[],[f121966,f81297,f128607])).
% 44.14/5.93  fof(f81297,plain,(
% 44.14/5.93    spl9_76 <=> r2_hidden(sK6(sK2,sK0),sK2)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_76])])).
% 44.14/5.93  fof(f121966,plain,(
% 44.14/5.93    sK2 = k4_xboole_0(sK2,k1_tarski(sK6(sK2,sK0))) | spl9_76),
% 44.14/5.93    inference(resolution,[],[f81299,f111163])).
% 44.14/5.93  fof(f81299,plain,(
% 44.14/5.93    ~r2_hidden(sK6(sK2,sK0),sK2) | spl9_76),
% 44.14/5.93    inference(avatar_component_clause,[],[f81297])).
% 44.14/5.93  fof(f128605,plain,(
% 44.14/5.93    spl9_128 | spl9_76),
% 44.14/5.93    inference(avatar_split_clause,[],[f121952,f81297,f128602])).
% 44.14/5.93  fof(f128602,plain,(
% 44.14/5.93    spl9_128 <=> k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(sK6(sK2,sK0)))),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_128])])).
% 44.14/5.93  fof(f121952,plain,(
% 44.14/5.93    k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(sK6(sK2,sK0))) | spl9_76),
% 44.14/5.93    inference(resolution,[],[f81299,f1331])).
% 44.14/5.93  fof(f128301,plain,(
% 44.14/5.93    spl9_127 | ~spl9_77),
% 44.14/5.93    inference(avatar_split_clause,[],[f81342,f81302,f128298])).
% 44.14/5.93  fof(f128298,plain,(
% 44.14/5.93    spl9_127 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(sK2,sK0)),sK0)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_127])])).
% 44.14/5.93  fof(f81342,plain,(
% 44.14/5.93    k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(sK2,sK0)),sK0) | ~spl9_77),
% 44.14/5.93    inference(resolution,[],[f81304,f26029])).
% 44.14/5.93  fof(f127800,plain,(
% 44.14/5.93    spl9_126 | ~spl9_123),
% 44.14/5.93    inference(avatar_split_clause,[],[f126562,f122817,f127797])).
% 44.14/5.93  fof(f127797,plain,(
% 44.14/5.93    spl9_126 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK0,k1_xboole_0)),sK2)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_126])])).
% 44.14/5.93  fof(f126562,plain,(
% 44.14/5.93    k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK0,k1_xboole_0)),sK2) | ~spl9_123),
% 44.14/5.93    inference(resolution,[],[f122819,f26029])).
% 44.14/5.93  fof(f127795,plain,(
% 44.14/5.93    spl9_125 | spl9_122),
% 44.14/5.93    inference(avatar_split_clause,[],[f126356,f122813,f127792])).
% 44.14/5.93  fof(f127792,plain,(
% 44.14/5.93    spl9_125 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK0,k1_xboole_0)),sK0)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_125])])).
% 44.14/5.93  fof(f122813,plain,(
% 44.14/5.93    spl9_122 <=> r1_tarski(sK0,k1_xboole_0)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_122])])).
% 44.14/5.93  fof(f126356,plain,(
% 44.14/5.93    k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK0,k1_xboole_0)),sK0) | spl9_122),
% 44.14/5.93    inference(resolution,[],[f122814,f1637])).
% 44.14/5.93  fof(f1637,plain,(
% 44.14/5.93    ( ! [X28,X27] : (r1_tarski(X27,X28) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(X27,X28)),X27)) )),
% 44.14/5.93    inference(resolution,[],[f1304,f122])).
% 44.14/5.93  fof(f122814,plain,(
% 44.14/5.93    ~r1_tarski(sK0,k1_xboole_0) | spl9_122),
% 44.14/5.93    inference(avatar_component_clause,[],[f122813])).
% 44.14/5.93  fof(f126950,plain,(
% 44.14/5.93    spl9_124 | ~spl9_73 | ~spl9_123),
% 44.14/5.93    inference(avatar_split_clause,[],[f126902,f122817,f78248,f126947])).
% 44.14/5.93  fof(f126902,plain,(
% 44.14/5.93    r2_hidden(sK4(sK0,k1_xboole_0),sK0) | (~spl9_73 | ~spl9_123)),
% 44.14/5.93    inference(resolution,[],[f80905,f122819])).
% 44.14/5.93  fof(f80905,plain,(
% 44.14/5.93    ( ! [X11] : (~r2_hidden(X11,sK2) | r2_hidden(X11,sK0)) ) | ~spl9_73),
% 44.14/5.93    inference(superposition,[],[f90,f78250])).
% 44.14/5.93  fof(f126346,plain,(
% 44.14/5.93    spl9_1 | ~spl9_122),
% 44.14/5.93    inference(avatar_split_clause,[],[f122823,f122813,f93])).
% 44.14/5.93  fof(f93,plain,(
% 44.14/5.93    spl9_1 <=> k1_xboole_0 = sK0),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 44.14/5.93  fof(f122823,plain,(
% 44.14/5.93    k1_xboole_0 = sK0 | ~spl9_122),
% 44.14/5.93    inference(forward_demodulation,[],[f122822,f126])).
% 44.14/5.93  fof(f122822,plain,(
% 44.14/5.93    sK0 = k3_xboole_0(sK0,k1_xboole_0) | ~spl9_122),
% 44.14/5.93    inference(resolution,[],[f122815,f54])).
% 44.14/5.93  fof(f122815,plain,(
% 44.14/5.93    r1_tarski(sK0,k1_xboole_0) | ~spl9_122),
% 44.14/5.93    inference(avatar_component_clause,[],[f122813])).
% 44.14/5.93  fof(f122820,plain,(
% 44.14/5.93    spl9_122 | spl9_123 | ~spl9_16),
% 44.14/5.93    inference(avatar_split_clause,[],[f121663,f5863,f122817,f122813])).
% 44.14/5.93  fof(f5863,plain,(
% 44.14/5.93    spl9_16 <=> k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 44.14/5.93  fof(f121663,plain,(
% 44.14/5.93    r2_hidden(sK4(sK0,k1_xboole_0),sK2) | r1_tarski(sK0,k1_xboole_0) | ~spl9_16),
% 44.14/5.93    inference(superposition,[],[f83321,f5865])).
% 44.14/5.93  fof(f5865,plain,(
% 44.14/5.93    k1_xboole_0 = k4_xboole_0(sK0,sK2) | ~spl9_16),
% 44.14/5.93    inference(avatar_component_clause,[],[f5863])).
% 44.14/5.93  fof(f121982,plain,(
% 44.14/5.93    spl9_121 | ~spl9_4 | ~spl9_117),
% 44.14/5.93    inference(avatar_split_clause,[],[f120737,f117405,f107,f121979])).
% 44.14/5.93  fof(f117405,plain,(
% 44.14/5.93    spl9_117 <=> r2_hidden(sK6(sK3,sK1),sK3)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_117])])).
% 44.14/5.93  fof(f120737,plain,(
% 44.14/5.93    r2_hidden(sK6(sK1,sK1),sK1) | (~spl9_4 | ~spl9_117)),
% 44.14/5.93    inference(backward_demodulation,[],[f117406,f108])).
% 44.14/5.93  fof(f117406,plain,(
% 44.14/5.93    r2_hidden(sK6(sK3,sK1),sK3) | ~spl9_117),
% 44.14/5.93    inference(avatar_component_clause,[],[f117405])).
% 44.14/5.93  fof(f121507,plain,(
% 44.14/5.93    ~spl9_120 | ~spl9_4 | spl9_116),
% 44.14/5.93    inference(avatar_split_clause,[],[f120736,f117398,f107,f121504])).
% 44.14/5.93  fof(f121504,plain,(
% 44.14/5.93    spl9_120 <=> r2_xboole_0(sK1,sK1)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_120])])).
% 44.14/5.93  fof(f117398,plain,(
% 44.14/5.93    spl9_116 <=> r2_xboole_0(sK3,sK1)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_116])])).
% 44.14/5.93  fof(f120736,plain,(
% 44.14/5.93    ~r2_xboole_0(sK1,sK1) | (~spl9_4 | spl9_116)),
% 44.14/5.93    inference(backward_demodulation,[],[f117399,f108])).
% 44.14/5.93  fof(f117399,plain,(
% 44.14/5.93    ~r2_xboole_0(sK3,sK1) | spl9_116),
% 44.14/5.93    inference(avatar_component_clause,[],[f117398])).
% 44.14/5.93  fof(f118934,plain,(
% 44.14/5.93    ~spl9_119),
% 44.14/5.93    inference(avatar_contradiction_clause,[],[f118921])).
% 44.14/5.93  fof(f118921,plain,(
% 44.14/5.93    $false | ~spl9_119),
% 44.14/5.93    inference(resolution,[],[f118919,f123])).
% 44.14/5.93  fof(f118919,plain,(
% 44.14/5.93    r2_hidden(sK6(sK3,sK1),k1_xboole_0) | ~spl9_119),
% 44.14/5.93    inference(avatar_component_clause,[],[f118917])).
% 44.14/5.93  fof(f118917,plain,(
% 44.14/5.93    spl9_119 <=> r2_hidden(sK6(sK3,sK1),k1_xboole_0)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_119])])).
% 44.14/5.93  fof(f118920,plain,(
% 44.14/5.93    spl9_119 | ~spl9_11 | spl9_117 | ~spl9_118),
% 44.14/5.93    inference(avatar_split_clause,[],[f118013,f117410,f117405,f3321,f118917])).
% 44.14/5.93  fof(f3321,plain,(
% 44.14/5.93    spl9_11 <=> ! [X2] : k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(X2,sK3))),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 44.14/5.93  fof(f118013,plain,(
% 44.14/5.93    r2_hidden(sK6(sK3,sK1),k1_xboole_0) | (~spl9_11 | spl9_117 | ~spl9_118)),
% 44.14/5.93    inference(forward_demodulation,[],[f118005,f117971])).
% 44.14/5.93  fof(f117971,plain,(
% 44.14/5.93    k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK6(sK3,sK1))) | (~spl9_11 | spl9_117)),
% 44.14/5.93    inference(resolution,[],[f117407,f108879])).
% 44.14/5.93  fof(f108879,plain,(
% 44.14/5.93    ( ! [X0] : (r2_hidden(X0,sK3) | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(X0))) ) | ~spl9_11),
% 44.14/5.93    inference(condensation,[],[f108778])).
% 44.14/5.93  fof(f108778,plain,(
% 44.14/5.93    ( ! [X47,X48] : (r2_hidden(X47,sK3) | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(X47)) | k1_xboole_0 = k3_xboole_0(X48,k1_tarski(X47))) ) | ~spl9_11),
% 44.14/5.93    inference(resolution,[],[f84580,f1331])).
% 44.14/5.93  fof(f84580,plain,(
% 44.14/5.93    ( ! [X4,X5] : (~r2_hidden(X4,X5) | r2_hidden(X4,sK3) | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(X4))) ) | ~spl9_11),
% 44.14/5.93    inference(backward_demodulation,[],[f46580,f84413])).
% 44.14/5.93  fof(f46580,plain,(
% 44.14/5.93    ( ! [X4,X5] : (~r2_hidden(X4,k4_xboole_0(X5,k1_xboole_0)) | r2_hidden(X4,sK3) | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(X4))) ) | ~spl9_11),
% 44.14/5.93    inference(superposition,[],[f188,f46200])).
% 44.14/5.93  fof(f46200,plain,(
% 44.14/5.93    ( ! [X482] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X482),sK3) | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(X482))) ) | ~spl9_11),
% 44.14/5.93    inference(superposition,[],[f3322,f41576])).
% 44.14/5.93  fof(f3322,plain,(
% 44.14/5.93    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(X2,sK3))) ) | ~spl9_11),
% 44.14/5.93    inference(avatar_component_clause,[],[f3321])).
% 44.14/5.93  fof(f117407,plain,(
% 44.14/5.93    ~r2_hidden(sK6(sK3,sK1),sK3) | spl9_117),
% 44.14/5.93    inference(avatar_component_clause,[],[f117405])).
% 44.14/5.93  fof(f118005,plain,(
% 44.14/5.93    r2_hidden(sK6(sK3,sK1),k3_xboole_0(sK1,k1_tarski(sK6(sK3,sK1)))) | ~spl9_118),
% 44.14/5.93    inference(resolution,[],[f117412,f192])).
% 44.14/5.93  fof(f118016,plain,(
% 44.14/5.93    spl9_114 | ~spl9_115),
% 44.14/5.93    inference(avatar_split_clause,[],[f117277,f117249,f116740])).
% 44.14/5.93  fof(f116740,plain,(
% 44.14/5.93    spl9_114 <=> sK3 = k3_xboole_0(sK3,sK1)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_114])])).
% 44.14/5.93  fof(f117249,plain,(
% 44.14/5.93    spl9_115 <=> sK3 = k3_xboole_0(sK1,sK3)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_115])])).
% 44.14/5.93  fof(f117277,plain,(
% 44.14/5.93    sK3 = k3_xboole_0(sK3,sK1) | ~spl9_115),
% 44.14/5.93    inference(superposition,[],[f273,f117251])).
% 44.14/5.93  fof(f117251,plain,(
% 44.14/5.93    sK3 = k3_xboole_0(sK1,sK3) | ~spl9_115),
% 44.14/5.93    inference(avatar_component_clause,[],[f117249])).
% 44.14/5.93  fof(f117828,plain,(
% 44.14/5.93    spl9_112 | ~spl9_115),
% 44.14/5.93    inference(avatar_split_clause,[],[f117275,f117249,f116729])).
% 44.14/5.93  fof(f116729,plain,(
% 44.14/5.93    spl9_112 <=> r1_tarski(sK3,sK1)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_112])])).
% 44.14/5.93  fof(f117275,plain,(
% 44.14/5.93    r1_tarski(sK3,sK1) | ~spl9_115),
% 44.14/5.93    inference(superposition,[],[f266,f117251])).
% 44.14/5.93  fof(f117441,plain,(
% 44.14/5.93    ~spl9_113),
% 44.14/5.93    inference(avatar_contradiction_clause,[],[f117428])).
% 44.14/5.93  fof(f117428,plain,(
% 44.14/5.93    $false | ~spl9_113),
% 44.14/5.93    inference(resolution,[],[f116735,f123])).
% 44.14/5.93  fof(f116735,plain,(
% 44.14/5.93    r2_hidden(sK4(sK3,sK1),k1_xboole_0) | ~spl9_113),
% 44.14/5.93    inference(avatar_component_clause,[],[f116733])).
% 44.14/5.93  fof(f116733,plain,(
% 44.14/5.93    spl9_113 <=> r2_hidden(sK4(sK3,sK1),k1_xboole_0)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_113])])).
% 44.14/5.93  fof(f117426,plain,(
% 44.14/5.93    spl9_112 | ~spl9_115),
% 44.14/5.93    inference(avatar_split_clause,[],[f117275,f117249,f116729])).
% 44.14/5.93  fof(f117413,plain,(
% 44.14/5.93    spl9_118 | ~spl9_116),
% 44.14/5.93    inference(avatar_split_clause,[],[f117403,f117398,f117410])).
% 44.14/5.93  fof(f117403,plain,(
% 44.14/5.93    r2_hidden(sK6(sK3,sK1),sK1) | ~spl9_116),
% 44.14/5.93    inference(resolution,[],[f117400,f65])).
% 44.14/5.93  fof(f117400,plain,(
% 44.14/5.93    r2_xboole_0(sK3,sK1) | ~spl9_116),
% 44.14/5.93    inference(avatar_component_clause,[],[f117398])).
% 44.14/5.93  fof(f117408,plain,(
% 44.14/5.93    ~spl9_117 | ~spl9_116),
% 44.14/5.93    inference(avatar_split_clause,[],[f117402,f117398,f117405])).
% 44.14/5.93  fof(f117402,plain,(
% 44.14/5.93    ~r2_hidden(sK6(sK3,sK1),sK3) | ~spl9_116),
% 44.14/5.93    inference(resolution,[],[f117400,f66])).
% 44.14/5.93  fof(f66,plain,(
% 44.14/5.93    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | ~r2_hidden(sK6(X0,X1),X0)) )),
% 44.14/5.93    inference(cnf_transformation,[],[f36])).
% 44.14/5.93  fof(f117401,plain,(
% 44.14/5.93    spl9_116 | spl9_4 | ~spl9_112),
% 44.14/5.93    inference(avatar_split_clause,[],[f116737,f116729,f107,f117398])).
% 44.14/5.93  fof(f116737,plain,(
% 44.14/5.93    sK1 = sK3 | r2_xboole_0(sK3,sK1) | ~spl9_112),
% 44.14/5.93    inference(resolution,[],[f116731,f55])).
% 44.14/5.93  fof(f116731,plain,(
% 44.14/5.93    r1_tarski(sK3,sK1) | ~spl9_112),
% 44.14/5.93    inference(avatar_component_clause,[],[f116729])).
% 44.14/5.93  fof(f117252,plain,(
% 44.14/5.93    spl9_115 | ~spl9_114),
% 44.14/5.93    inference(avatar_split_clause,[],[f116744,f116740,f117249])).
% 44.14/5.93  fof(f116744,plain,(
% 44.14/5.93    sK3 = k3_xboole_0(sK1,sK3) | ~spl9_114),
% 44.14/5.93    inference(superposition,[],[f116742,f53])).
% 44.14/5.93  fof(f116742,plain,(
% 44.14/5.93    sK3 = k3_xboole_0(sK3,sK1) | ~spl9_114),
% 44.14/5.93    inference(avatar_component_clause,[],[f116740])).
% 44.14/5.93  fof(f116743,plain,(
% 44.14/5.93    spl9_114 | ~spl9_112),
% 44.14/5.93    inference(avatar_split_clause,[],[f116738,f116729,f116740])).
% 44.14/5.93  fof(f116738,plain,(
% 44.14/5.93    sK3 = k3_xboole_0(sK3,sK1) | ~spl9_112),
% 44.14/5.93    inference(resolution,[],[f116731,f54])).
% 44.14/5.93  fof(f116736,plain,(
% 44.14/5.93    spl9_112 | spl9_113 | ~spl9_13),
% 44.14/5.93    inference(avatar_split_clause,[],[f116725,f3921,f116733,f116729])).
% 44.14/5.93  fof(f3921,plain,(
% 44.14/5.93    spl9_13 <=> k1_xboole_0 = k4_xboole_0(sK3,sK1)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 44.14/5.93  fof(f116725,plain,(
% 44.14/5.93    r2_hidden(sK4(sK3,sK1),k1_xboole_0) | r1_tarski(sK3,sK1) | ~spl9_13),
% 44.14/5.93    inference(duplicate_literal_removal,[],[f116710])).
% 44.14/5.93  fof(f116710,plain,(
% 44.14/5.93    r2_hidden(sK4(sK3,sK1),k1_xboole_0) | r1_tarski(sK3,sK1) | r1_tarski(sK3,sK1) | ~spl9_13),
% 44.14/5.93    inference(resolution,[],[f83312,f57])).
% 44.14/5.93  fof(f83312,plain,(
% 44.14/5.93    ( ! [X47] : (r2_hidden(sK4(sK3,X47),sK1) | r2_hidden(sK4(sK3,X47),k1_xboole_0) | r1_tarski(sK3,X47)) ) | ~spl9_13),
% 44.14/5.93    inference(superposition,[],[f183,f3923])).
% 44.14/5.93  fof(f3923,plain,(
% 44.14/5.93    k1_xboole_0 = k4_xboole_0(sK3,sK1) | ~spl9_13),
% 44.14/5.93    inference(avatar_component_clause,[],[f3921])).
% 44.14/5.93  fof(f116207,plain,(
% 44.14/5.93    ~spl9_61 | ~spl9_36 | spl9_59 | ~spl9_73),
% 44.14/5.93    inference(avatar_split_clause,[],[f80318,f78248,f60577,f11051,f62743])).
% 44.14/5.93  fof(f62743,plain,(
% 44.14/5.93    spl9_61 <=> r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_61])])).
% 44.14/5.93  fof(f11051,plain,(
% 44.14/5.93    spl9_36 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).
% 44.14/5.93  fof(f60577,plain,(
% 44.14/5.93    spl9_59 <=> r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)),k2_zfmisc_1(sK0,sK1))),
% 44.14/5.93    introduced(avatar_definition,[new_symbols(naming,[spl9_59])])).
% 44.14/5.93  fof(f80318,plain,(
% 44.14/5.93    ~r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) | (~spl9_36 | spl9_59 | ~spl9_73)),
% 44.14/5.93    inference(backward_demodulation,[],[f60579,f79712])).
% 44.14/5.93  fof(f79712,plain,(
% 44.14/5.93    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1) | (~spl9_36 | ~spl9_73)),
% 44.14/5.93    inference(backward_demodulation,[],[f11053,f78250])).
% 44.14/5.93  fof(f11053,plain,(
% 44.14/5.93    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) | ~spl9_36),
% 44.14/5.93    inference(avatar_component_clause,[],[f11051])).
% 44.14/5.93  fof(f60579,plain,(
% 44.14/5.93    ~r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)),k2_zfmisc_1(sK0,sK1)) | spl9_59),
% 44.14/5.93    inference(avatar_component_clause,[],[f60577])).
% 44.14/5.93  fof(f105943,plain,(
% 44.14/5.93    spl9_111 | ~spl9_99),
% 44.14/5.93    inference(avatar_split_clause,[],[f96687,f96677,f105940])).
% 44.14/5.94  fof(f105940,plain,(
% 44.14/5.94    spl9_111 <=> r2_hidden(sK4(sK3,k1_xboole_0),k3_xboole_0(k3_xboole_0(sK1,sK3),k1_tarski(sK4(sK3,k1_xboole_0))))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_111])])).
% 44.14/5.94  fof(f96677,plain,(
% 44.14/5.94    spl9_99 <=> r2_hidden(sK4(sK3,k1_xboole_0),k3_xboole_0(sK1,sK3))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_99])])).
% 44.14/5.94  fof(f96687,plain,(
% 44.14/5.94    r2_hidden(sK4(sK3,k1_xboole_0),k3_xboole_0(k3_xboole_0(sK1,sK3),k1_tarski(sK4(sK3,k1_xboole_0)))) | ~spl9_99),
% 44.14/5.94    inference(resolution,[],[f96679,f192])).
% 44.14/5.94  fof(f96679,plain,(
% 44.14/5.94    r2_hidden(sK4(sK3,k1_xboole_0),k3_xboole_0(sK1,sK3)) | ~spl9_99),
% 44.14/5.94    inference(avatar_component_clause,[],[f96677])).
% 44.14/5.94  fof(f102128,plain,(
% 44.14/5.94    spl9_110 | ~spl9_96),
% 44.14/5.94    inference(avatar_split_clause,[],[f96464,f96454,f102125])).
% 44.14/5.94  fof(f102125,plain,(
% 44.14/5.94    spl9_110 <=> r2_hidden(sK4(sK1,k1_xboole_0),k3_xboole_0(k3_xboole_0(sK1,sK3),k1_tarski(sK4(sK1,k1_xboole_0))))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_110])])).
% 44.14/5.94  fof(f96454,plain,(
% 44.14/5.94    spl9_96 <=> r2_hidden(sK4(sK1,k1_xboole_0),k3_xboole_0(sK1,sK3))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_96])])).
% 44.14/5.94  fof(f96464,plain,(
% 44.14/5.94    r2_hidden(sK4(sK1,k1_xboole_0),k3_xboole_0(k3_xboole_0(sK1,sK3),k1_tarski(sK4(sK1,k1_xboole_0)))) | ~spl9_96),
% 44.14/5.94    inference(resolution,[],[f96456,f192])).
% 44.14/5.94  fof(f96456,plain,(
% 44.14/5.94    r2_hidden(sK4(sK1,k1_xboole_0),k3_xboole_0(sK1,sK3)) | ~spl9_96),
% 44.14/5.94    inference(avatar_component_clause,[],[f96454])).
% 44.14/5.94  fof(f98586,plain,(
% 44.14/5.94    spl9_109 | ~spl9_100),
% 44.14/5.94    inference(avatar_split_clause,[],[f96701,f96693,f98583])).
% 44.14/5.94  fof(f98583,plain,(
% 44.14/5.94    spl9_109 <=> r2_hidden(sK4(sK3,k1_xboole_0),k3_xboole_0(sK3,k1_tarski(sK4(sK3,k1_xboole_0))))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_109])])).
% 44.14/5.94  fof(f96693,plain,(
% 44.14/5.94    spl9_100 <=> r2_hidden(sK4(sK3,k1_xboole_0),sK3)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_100])])).
% 44.14/5.94  fof(f96701,plain,(
% 44.14/5.94    r2_hidden(sK4(sK3,k1_xboole_0),k3_xboole_0(sK3,k1_tarski(sK4(sK3,k1_xboole_0)))) | ~spl9_100),
% 44.14/5.94    inference(resolution,[],[f96695,f192])).
% 44.14/5.94  fof(f96695,plain,(
% 44.14/5.94    r2_hidden(sK4(sK3,k1_xboole_0),sK3) | ~spl9_100),
% 44.14/5.94    inference(avatar_component_clause,[],[f96693])).
% 44.14/5.94  fof(f98581,plain,(
% 44.14/5.94    spl9_97 | spl9_108 | ~spl9_94),
% 44.14/5.94    inference(avatar_split_clause,[],[f95177,f95091,f98579,f96470])).
% 44.14/5.94  fof(f98579,plain,(
% 44.14/5.94    spl9_108 <=> ! [X1] : ~r2_hidden(sK4(sK1,k1_xboole_0),X1)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_108])])).
% 44.14/5.94  fof(f95091,plain,(
% 44.14/5.94    spl9_94 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK1,k1_xboole_0)),sK1)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_94])])).
% 44.14/5.94  fof(f95177,plain,(
% 44.14/5.94    ( ! [X1] : (~r2_hidden(sK4(sK1,k1_xboole_0),X1) | r2_hidden(sK4(sK1,k1_xboole_0),sK1)) ) | ~spl9_94),
% 44.14/5.94    inference(forward_demodulation,[],[f95103,f84413])).
% 44.14/5.94  fof(f95103,plain,(
% 44.14/5.94    ( ! [X1] : (~r2_hidden(sK4(sK1,k1_xboole_0),k4_xboole_0(X1,k1_xboole_0)) | r2_hidden(sK4(sK1,k1_xboole_0),sK1)) ) | ~spl9_94),
% 44.14/5.94    inference(superposition,[],[f188,f95093])).
% 44.14/5.94  fof(f95093,plain,(
% 44.14/5.94    k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK1,k1_xboole_0)),sK1) | ~spl9_94),
% 44.14/5.94    inference(avatar_component_clause,[],[f95091])).
% 44.14/5.94  fof(f98577,plain,(
% 44.14/5.94    spl9_97 | spl9_107 | ~spl9_94),
% 44.14/5.94    inference(avatar_split_clause,[],[f95101,f95091,f98574,f96470])).
% 44.14/5.94  fof(f98574,plain,(
% 44.14/5.94    spl9_107 <=> r2_hidden(sK4(sK1,k1_xboole_0),k1_xboole_0)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_107])])).
% 44.14/5.94  fof(f95101,plain,(
% 44.14/5.94    r2_hidden(sK4(sK1,k1_xboole_0),k1_xboole_0) | r2_hidden(sK4(sK1,k1_xboole_0),sK1) | ~spl9_94),
% 44.14/5.94    inference(superposition,[],[f182,f95093])).
% 44.14/5.94  fof(f98060,plain,(
% 44.14/5.94    spl9_106 | ~spl9_99),
% 44.14/5.94    inference(avatar_split_clause,[],[f96690,f96677,f98057])).
% 44.14/5.94  fof(f98057,plain,(
% 44.14/5.94    spl9_106 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK3,k1_xboole_0)),k3_xboole_0(sK1,sK3))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_106])])).
% 44.14/5.94  fof(f96690,plain,(
% 44.14/5.94    k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK3,k1_xboole_0)),k3_xboole_0(sK1,sK3)) | ~spl9_99),
% 44.14/5.94    inference(resolution,[],[f96679,f26029])).
% 44.14/5.94  fof(f98055,plain,(
% 44.14/5.94    spl9_100 | spl9_105 | ~spl9_92),
% 44.14/5.94    inference(avatar_split_clause,[],[f94976,f94890,f98053,f96693])).
% 44.14/5.94  fof(f98053,plain,(
% 44.14/5.94    spl9_105 <=> ! [X1] : ~r2_hidden(sK4(sK3,k1_xboole_0),X1)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_105])])).
% 44.14/5.94  fof(f94890,plain,(
% 44.14/5.94    spl9_92 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK3,k1_xboole_0)),sK3)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_92])])).
% 44.14/5.94  fof(f94976,plain,(
% 44.14/5.94    ( ! [X1] : (~r2_hidden(sK4(sK3,k1_xboole_0),X1) | r2_hidden(sK4(sK3,k1_xboole_0),sK3)) ) | ~spl9_92),
% 44.14/5.94    inference(forward_demodulation,[],[f94902,f84413])).
% 44.14/5.94  fof(f94902,plain,(
% 44.14/5.94    ( ! [X1] : (~r2_hidden(sK4(sK3,k1_xboole_0),k4_xboole_0(X1,k1_xboole_0)) | r2_hidden(sK4(sK3,k1_xboole_0),sK3)) ) | ~spl9_92),
% 44.14/5.94    inference(superposition,[],[f188,f94892])).
% 44.14/5.94  fof(f94892,plain,(
% 44.14/5.94    k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK3,k1_xboole_0)),sK3) | ~spl9_92),
% 44.14/5.94    inference(avatar_component_clause,[],[f94890])).
% 44.14/5.94  fof(f98051,plain,(
% 44.14/5.94    spl9_100 | spl9_104 | ~spl9_92),
% 44.14/5.94    inference(avatar_split_clause,[],[f94900,f94890,f98048,f96693])).
% 44.14/5.94  fof(f98048,plain,(
% 44.14/5.94    spl9_104 <=> r2_hidden(sK4(sK3,k1_xboole_0),k1_xboole_0)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_104])])).
% 44.14/5.94  fof(f94900,plain,(
% 44.14/5.94    r2_hidden(sK4(sK3,k1_xboole_0),k1_xboole_0) | r2_hidden(sK4(sK3,k1_xboole_0),sK3) | ~spl9_92),
% 44.14/5.94    inference(superposition,[],[f182,f94892])).
% 44.14/5.94  fof(f98046,plain,(
% 44.14/5.94    spl9_103 | ~spl9_91),
% 44.14/5.94    inference(avatar_split_clause,[],[f94150,f90285,f98043])).
% 44.14/5.94  fof(f98043,plain,(
% 44.14/5.94    spl9_103 <=> r2_hidden(sK4(sK1,k1_xboole_0),k3_xboole_0(sK3,k1_tarski(sK4(sK1,k1_xboole_0))))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_103])])).
% 44.14/5.94  fof(f90285,plain,(
% 44.14/5.94    spl9_91 <=> r2_hidden(sK4(sK1,k1_xboole_0),sK3)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_91])])).
% 44.14/5.94  fof(f94150,plain,(
% 44.14/5.94    r2_hidden(sK4(sK1,k1_xboole_0),k3_xboole_0(sK3,k1_tarski(sK4(sK1,k1_xboole_0)))) | ~spl9_91),
% 44.14/5.94    inference(resolution,[],[f90287,f192])).
% 44.14/5.94  fof(f90287,plain,(
% 44.14/5.94    r2_hidden(sK4(sK1,k1_xboole_0),sK3) | ~spl9_91),
% 44.14/5.94    inference(avatar_component_clause,[],[f90285])).
% 44.14/5.94  fof(f97209,plain,(
% 44.14/5.94    spl9_102 | ~spl9_97),
% 44.14/5.94    inference(avatar_split_clause,[],[f96478,f96470,f97206])).
% 44.14/5.94  fof(f97206,plain,(
% 44.14/5.94    spl9_102 <=> r2_hidden(sK4(sK1,k1_xboole_0),k3_xboole_0(sK1,k1_tarski(sK4(sK1,k1_xboole_0))))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_102])])).
% 44.14/5.94  fof(f96478,plain,(
% 44.14/5.94    r2_hidden(sK4(sK1,k1_xboole_0),k3_xboole_0(sK1,k1_tarski(sK4(sK1,k1_xboole_0)))) | ~spl9_97),
% 44.14/5.94    inference(resolution,[],[f96472,f192])).
% 44.14/5.94  fof(f97204,plain,(
% 44.14/5.94    spl9_101 | ~spl9_89),
% 44.14/5.94    inference(avatar_split_clause,[],[f89585,f85170,f97201])).
% 44.14/5.94  fof(f97201,plain,(
% 44.14/5.94    spl9_101 <=> r2_hidden(sK4(sK3,k1_xboole_0),k3_xboole_0(sK1,k1_tarski(sK4(sK3,k1_xboole_0))))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_101])])).
% 44.14/5.94  fof(f85170,plain,(
% 44.14/5.94    spl9_89 <=> r2_hidden(sK4(sK3,k1_xboole_0),sK1)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_89])])).
% 44.14/5.94  fof(f89585,plain,(
% 44.14/5.94    r2_hidden(sK4(sK3,k1_xboole_0),k3_xboole_0(sK1,k1_tarski(sK4(sK3,k1_xboole_0)))) | ~spl9_89),
% 44.14/5.94    inference(resolution,[],[f85172,f192])).
% 44.14/5.94  fof(f85172,plain,(
% 44.14/5.94    r2_hidden(sK4(sK3,k1_xboole_0),sK1) | ~spl9_89),
% 44.14/5.94    inference(avatar_component_clause,[],[f85170])).
% 44.14/5.94  fof(f96696,plain,(
% 44.14/5.94    spl9_100 | ~spl9_99),
% 44.14/5.94    inference(avatar_split_clause,[],[f96682,f96677,f96693])).
% 44.14/5.94  fof(f96682,plain,(
% 44.14/5.94    r2_hidden(sK4(sK3,k1_xboole_0),sK3) | ~spl9_99),
% 44.14/5.94    inference(resolution,[],[f96679,f89])).
% 44.14/5.94  fof(f96680,plain,(
% 44.14/5.94    spl9_88 | spl9_99 | ~spl9_43),
% 44.14/5.94    inference(avatar_split_clause,[],[f84337,f13386,f96677,f85166])).
% 44.14/5.94  fof(f85166,plain,(
% 44.14/5.94    spl9_88 <=> r1_tarski(sK3,k1_xboole_0)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_88])])).
% 44.14/5.94  fof(f13386,plain,(
% 44.14/5.94    spl9_43 <=> k1_xboole_0 = k4_xboole_0(sK3,k3_xboole_0(sK1,sK3))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).
% 44.14/5.94  fof(f84337,plain,(
% 44.14/5.94    r2_hidden(sK4(sK3,k1_xboole_0),k3_xboole_0(sK1,sK3)) | r1_tarski(sK3,k1_xboole_0) | ~spl9_43),
% 44.14/5.94    inference(superposition,[],[f83321,f13388])).
% 44.14/5.94  fof(f13388,plain,(
% 44.14/5.94    k1_xboole_0 = k4_xboole_0(sK3,k3_xboole_0(sK1,sK3)) | ~spl9_43),
% 44.14/5.94    inference(avatar_component_clause,[],[f13386])).
% 44.14/5.94  fof(f96580,plain,(
% 44.14/5.94    spl9_98 | ~spl9_96),
% 44.14/5.94    inference(avatar_split_clause,[],[f96467,f96454,f96577])).
% 44.14/5.94  fof(f96577,plain,(
% 44.14/5.94    spl9_98 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK1,k1_xboole_0)),k3_xboole_0(sK1,sK3))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_98])])).
% 44.14/5.94  fof(f96467,plain,(
% 44.14/5.94    k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK1,k1_xboole_0)),k3_xboole_0(sK1,sK3)) | ~spl9_96),
% 44.14/5.94    inference(resolution,[],[f96456,f26029])).
% 44.14/5.94  fof(f96473,plain,(
% 44.14/5.94    spl9_97 | ~spl9_96),
% 44.14/5.94    inference(avatar_split_clause,[],[f96458,f96454,f96470])).
% 44.14/5.94  fof(f96458,plain,(
% 44.14/5.94    r2_hidden(sK4(sK1,k1_xboole_0),sK1) | ~spl9_96),
% 44.14/5.94    inference(resolution,[],[f96456,f90])).
% 44.14/5.94  fof(f96457,plain,(
% 44.14/5.94    spl9_90 | spl9_96 | ~spl9_31),
% 44.14/5.94    inference(avatar_split_clause,[],[f84336,f9089,f96454,f90281])).
% 44.14/5.94  fof(f90281,plain,(
% 44.14/5.94    spl9_90 <=> r1_tarski(sK1,k1_xboole_0)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_90])])).
% 44.14/5.94  fof(f9089,plain,(
% 44.14/5.94    spl9_31 <=> k1_xboole_0 = k4_xboole_0(sK1,k3_xboole_0(sK1,sK3))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).
% 44.14/5.94  fof(f84336,plain,(
% 44.14/5.94    r2_hidden(sK4(sK1,k1_xboole_0),k3_xboole_0(sK1,sK3)) | r1_tarski(sK1,k1_xboole_0) | ~spl9_31),
% 44.14/5.94    inference(superposition,[],[f83321,f9091])).
% 44.14/5.94  fof(f9091,plain,(
% 44.14/5.94    k1_xboole_0 = k4_xboole_0(sK1,k3_xboole_0(sK1,sK3)) | ~spl9_31),
% 44.14/5.94    inference(avatar_component_clause,[],[f9089])).
% 44.14/5.94  fof(f95099,plain,(
% 44.14/5.94    spl9_95 | ~spl9_91),
% 44.14/5.94    inference(avatar_split_clause,[],[f94153,f90285,f95096])).
% 44.14/5.94  fof(f95096,plain,(
% 44.14/5.94    spl9_95 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK1,k1_xboole_0)),sK3)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_95])])).
% 44.14/5.94  fof(f94153,plain,(
% 44.14/5.94    k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK1,k1_xboole_0)),sK3) | ~spl9_91),
% 44.14/5.94    inference(resolution,[],[f90287,f26029])).
% 44.14/5.94  fof(f95094,plain,(
% 44.14/5.94    spl9_94 | spl9_90),
% 44.14/5.94    inference(avatar_split_clause,[],[f93964,f90281,f95091])).
% 44.14/5.94  fof(f93964,plain,(
% 44.14/5.94    k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK1,k1_xboole_0)),sK1) | spl9_90),
% 44.14/5.94    inference(resolution,[],[f90282,f1637])).
% 44.14/5.94  fof(f90282,plain,(
% 44.14/5.94    ~r1_tarski(sK1,k1_xboole_0) | spl9_90),
% 44.14/5.94    inference(avatar_component_clause,[],[f90281])).
% 44.14/5.94  fof(f94898,plain,(
% 44.14/5.94    spl9_93 | ~spl9_89),
% 44.14/5.94    inference(avatar_split_clause,[],[f89588,f85170,f94895])).
% 44.14/5.94  fof(f94895,plain,(
% 44.14/5.94    spl9_93 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK3,k1_xboole_0)),sK1)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_93])])).
% 44.14/5.94  fof(f89588,plain,(
% 44.14/5.94    k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK3,k1_xboole_0)),sK1) | ~spl9_89),
% 44.14/5.94    inference(resolution,[],[f85172,f26029])).
% 44.14/5.94  fof(f94893,plain,(
% 44.14/5.94    spl9_92 | spl9_88),
% 44.14/5.94    inference(avatar_split_clause,[],[f89408,f85166,f94890])).
% 44.14/5.94  fof(f89408,plain,(
% 44.14/5.94    k1_xboole_0 = k4_xboole_0(k1_tarski(sK4(sK3,k1_xboole_0)),sK3) | spl9_88),
% 44.14/5.94    inference(resolution,[],[f85167,f1637])).
% 44.14/5.94  fof(f85167,plain,(
% 44.14/5.94    ~r1_tarski(sK3,k1_xboole_0) | spl9_88),
% 44.14/5.94    inference(avatar_component_clause,[],[f85166])).
% 44.14/5.94  fof(f93954,plain,(
% 44.14/5.94    spl9_2 | ~spl9_90),
% 44.14/5.94    inference(avatar_split_clause,[],[f90291,f90281,f98])).
% 44.14/5.94  fof(f90291,plain,(
% 44.14/5.94    k1_xboole_0 = sK1 | ~spl9_90),
% 44.14/5.94    inference(forward_demodulation,[],[f90290,f126])).
% 44.14/5.94  fof(f90290,plain,(
% 44.14/5.94    sK1 = k3_xboole_0(sK1,k1_xboole_0) | ~spl9_90),
% 44.14/5.94    inference(resolution,[],[f90283,f54])).
% 44.14/5.94  fof(f90283,plain,(
% 44.14/5.94    r1_tarski(sK1,k1_xboole_0) | ~spl9_90),
% 44.14/5.94    inference(avatar_component_clause,[],[f90281])).
% 44.14/5.94  fof(f90288,plain,(
% 44.14/5.94    spl9_90 | spl9_91 | ~spl9_10),
% 44.14/5.94    inference(avatar_split_clause,[],[f84346,f3268,f90285,f90281])).
% 44.14/5.94  fof(f3268,plain,(
% 44.14/5.94    spl9_10 <=> k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 44.14/5.94  fof(f84346,plain,(
% 44.14/5.94    r2_hidden(sK4(sK1,k1_xboole_0),sK3) | r1_tarski(sK1,k1_xboole_0) | ~spl9_10),
% 44.14/5.94    inference(superposition,[],[f83321,f3270])).
% 44.14/5.94  fof(f3270,plain,(
% 44.14/5.94    k1_xboole_0 = k4_xboole_0(sK1,sK3) | ~spl9_10),
% 44.14/5.94    inference(avatar_component_clause,[],[f3268])).
% 44.14/5.94  fof(f89398,plain,(
% 44.14/5.94    spl9_6 | ~spl9_88),
% 44.14/5.94    inference(avatar_split_clause,[],[f85176,f85166,f170])).
% 44.14/5.94  fof(f170,plain,(
% 44.14/5.94    spl9_6 <=> k1_xboole_0 = sK3),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 44.14/5.94  fof(f85176,plain,(
% 44.14/5.94    k1_xboole_0 = sK3 | ~spl9_88),
% 44.14/5.94    inference(forward_demodulation,[],[f85175,f126])).
% 44.14/5.94  fof(f85175,plain,(
% 44.14/5.94    sK3 = k3_xboole_0(sK3,k1_xboole_0) | ~spl9_88),
% 44.14/5.94    inference(resolution,[],[f85168,f54])).
% 44.14/5.94  fof(f85168,plain,(
% 44.14/5.94    r1_tarski(sK3,k1_xboole_0) | ~spl9_88),
% 44.14/5.94    inference(avatar_component_clause,[],[f85166])).
% 44.14/5.94  fof(f85173,plain,(
% 44.14/5.94    spl9_88 | spl9_89 | ~spl9_13),
% 44.14/5.94    inference(avatar_split_clause,[],[f84344,f3921,f85170,f85166])).
% 44.14/5.94  fof(f84344,plain,(
% 44.14/5.94    r2_hidden(sK4(sK3,k1_xboole_0),sK1) | r1_tarski(sK3,k1_xboole_0) | ~spl9_13),
% 44.14/5.94    inference(superposition,[],[f83321,f3923])).
% 44.14/5.94  fof(f83349,plain,(
% 44.14/5.94    spl9_87 | ~spl9_3 | ~spl9_77),
% 44.14/5.94    inference(avatar_split_clause,[],[f82639,f81302,f103,f83346])).
% 44.14/5.94  fof(f83346,plain,(
% 44.14/5.94    spl9_87 <=> r2_hidden(sK6(sK0,sK0),k3_xboole_0(sK0,k1_tarski(sK6(sK0,sK0))))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_87])])).
% 44.14/5.94  fof(f103,plain,(
% 44.14/5.94    spl9_3 <=> sK0 = sK2),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 44.14/5.94  fof(f82639,plain,(
% 44.14/5.94    r2_hidden(sK6(sK0,sK0),k3_xboole_0(sK0,k1_tarski(sK6(sK0,sK0)))) | (~spl9_3 | ~spl9_77)),
% 44.14/5.94    inference(backward_demodulation,[],[f81338,f104])).
% 44.14/5.94  fof(f104,plain,(
% 44.14/5.94    sK0 = sK2 | ~spl9_3),
% 44.14/5.94    inference(avatar_component_clause,[],[f103])).
% 44.14/5.94  fof(f81338,plain,(
% 44.14/5.94    r2_hidden(sK6(sK2,sK0),k3_xboole_0(sK0,k1_tarski(sK6(sK2,sK0)))) | ~spl9_77),
% 44.14/5.94    inference(resolution,[],[f81304,f192])).
% 44.14/5.94  fof(f83327,plain,(
% 44.14/5.94    spl9_86 | ~spl9_3 | ~spl9_78),
% 44.14/5.94    inference(avatar_split_clause,[],[f82689,f81578,f103,f83324])).
% 44.14/5.94  fof(f83324,plain,(
% 44.14/5.94    spl9_86 <=> r2_hidden(sK6(k1_xboole_0,sK0),k3_xboole_0(sK0,k1_tarski(sK6(k1_xboole_0,sK0))))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_86])])).
% 44.14/5.94  fof(f82689,plain,(
% 44.14/5.94    r2_hidden(sK6(k1_xboole_0,sK0),k3_xboole_0(sK0,k1_tarski(sK6(k1_xboole_0,sK0)))) | (~spl9_3 | ~spl9_78)),
% 44.14/5.94    inference(backward_demodulation,[],[f81586,f104])).
% 44.14/5.94  fof(f81586,plain,(
% 44.14/5.94    r2_hidden(sK6(k1_xboole_0,sK2),k3_xboole_0(sK0,k1_tarski(sK6(k1_xboole_0,sK2)))) | ~spl9_78),
% 44.14/5.94    inference(resolution,[],[f81580,f192])).
% 44.14/5.94  fof(f83168,plain,(
% 44.14/5.94    spl9_85 | ~spl9_3 | ~spl9_77),
% 44.14/5.94    inference(avatar_split_clause,[],[f82642,f81302,f103,f83165])).
% 44.14/5.94  fof(f83165,plain,(
% 44.14/5.94    spl9_85 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(sK0,sK0)),sK0)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_85])])).
% 44.14/5.94  fof(f82642,plain,(
% 44.14/5.94    k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(sK0,sK0)),sK0) | (~spl9_3 | ~spl9_77)),
% 44.14/5.94    inference(backward_demodulation,[],[f81342,f104])).
% 44.14/5.94  fof(f83073,plain,(
% 44.14/5.94    spl9_84 | ~spl9_3 | ~spl9_79),
% 44.14/5.94    inference(avatar_split_clause,[],[f82721,f81640,f103,f83070])).
% 44.14/5.94  fof(f83070,plain,(
% 44.14/5.94    spl9_84 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k1_xboole_0,sK0)),sK0)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_84])])).
% 44.14/5.94  fof(f81640,plain,(
% 44.14/5.94    spl9_79 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k1_xboole_0,sK2)),sK0)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_79])])).
% 44.14/5.94  fof(f82721,plain,(
% 44.14/5.94    k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k1_xboole_0,sK0)),sK0) | (~spl9_3 | ~spl9_79)),
% 44.14/5.94    inference(backward_demodulation,[],[f81642,f104])).
% 44.14/5.94  fof(f81642,plain,(
% 44.14/5.94    k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k1_xboole_0,sK2)),sK0) | ~spl9_79),
% 44.14/5.94    inference(avatar_component_clause,[],[f81640])).
% 44.14/5.94  fof(f82972,plain,(
% 44.14/5.94    spl9_83 | ~spl9_3 | ~spl9_76),
% 44.14/5.94    inference(avatar_split_clause,[],[f82633,f81297,f103,f82969])).
% 44.14/5.94  fof(f82969,plain,(
% 44.14/5.94    spl9_83 <=> r2_hidden(sK6(sK0,sK0),sK0)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_83])])).
% 44.14/5.94  fof(f82633,plain,(
% 44.14/5.94    r2_hidden(sK6(sK0,sK0),sK0) | (~spl9_3 | ~spl9_76)),
% 44.14/5.94    inference(backward_demodulation,[],[f81298,f104])).
% 44.14/5.94  fof(f81298,plain,(
% 44.14/5.94    r2_hidden(sK6(sK2,sK0),sK2) | ~spl9_76),
% 44.14/5.94    inference(avatar_component_clause,[],[f81297])).
% 44.14/5.94  fof(f82957,plain,(
% 44.14/5.94    spl9_82 | ~spl9_3 | ~spl9_78),
% 44.14/5.94    inference(avatar_split_clause,[],[f82684,f81578,f103,f82954])).
% 44.14/5.94  fof(f82954,plain,(
% 44.14/5.94    spl9_82 <=> r2_hidden(sK6(k1_xboole_0,sK0),sK0)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_82])])).
% 44.14/5.94  fof(f82684,plain,(
% 44.14/5.94    r2_hidden(sK6(k1_xboole_0,sK0),sK0) | (~spl9_3 | ~spl9_78)),
% 44.14/5.94    inference(backward_demodulation,[],[f81580,f104])).
% 44.14/5.94  fof(f82952,plain,(
% 44.14/5.94    ~spl9_81 | ~spl9_3 | spl9_75),
% 44.14/5.94    inference(avatar_split_clause,[],[f82632,f81290,f103,f82949])).
% 44.14/5.94  fof(f82949,plain,(
% 44.14/5.94    spl9_81 <=> r2_xboole_0(sK0,sK0)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_81])])).
% 44.14/5.94  fof(f81290,plain,(
% 44.14/5.94    spl9_75 <=> r2_xboole_0(sK2,sK0)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_75])])).
% 44.14/5.94  fof(f82632,plain,(
% 44.14/5.94    ~r2_xboole_0(sK0,sK0) | (~spl9_3 | spl9_75)),
% 44.14/5.94    inference(backward_demodulation,[],[f81291,f104])).
% 44.14/5.94  fof(f81291,plain,(
% 44.14/5.94    ~r2_xboole_0(sK2,sK0) | spl9_75),
% 44.14/5.94    inference(avatar_component_clause,[],[f81290])).
% 44.14/5.94  fof(f81748,plain,(
% 44.14/5.94    spl9_80 | spl9_76),
% 44.14/5.94    inference(avatar_split_clause,[],[f81307,f81297,f81745])).
% 44.14/5.94  fof(f81745,plain,(
% 44.14/5.94    spl9_80 <=> k1_xboole_0 = k3_xboole_0(k1_tarski(sK6(sK2,sK0)),sK2)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_80])])).
% 44.14/5.94  fof(f81307,plain,(
% 44.14/5.94    k1_xboole_0 = k3_xboole_0(k1_tarski(sK6(sK2,sK0)),sK2) | spl9_76),
% 44.14/5.94    inference(resolution,[],[f81299,f963])).
% 44.14/5.94  fof(f81643,plain,(
% 44.14/5.94    spl9_79 | ~spl9_78),
% 44.14/5.94    inference(avatar_split_clause,[],[f81590,f81578,f81640])).
% 44.14/5.94  fof(f81590,plain,(
% 44.14/5.94    k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k1_xboole_0,sK2)),sK0) | ~spl9_78),
% 44.14/5.94    inference(resolution,[],[f81580,f26029])).
% 44.14/5.94  fof(f81638,plain,(
% 44.14/5.94    spl9_3 | spl9_77 | ~spl9_73),
% 44.14/5.94    inference(avatar_split_clause,[],[f80922,f78248,f81302,f103])).
% 44.14/5.94  fof(f80922,plain,(
% 44.14/5.94    r2_hidden(sK6(sK2,sK0),sK0) | sK0 = sK2 | ~spl9_73),
% 44.14/5.94    inference(superposition,[],[f375,f78250])).
% 44.14/5.94  fof(f375,plain,(
% 44.14/5.94    ( ! [X2,X3] : (r2_hidden(sK6(k3_xboole_0(X2,X3),X2),X2) | k3_xboole_0(X2,X3) = X2) )),
% 44.14/5.94    inference(resolution,[],[f272,f65])).
% 44.14/5.94  fof(f272,plain,(
% 44.14/5.94    ( ! [X0,X1] : (r2_xboole_0(k3_xboole_0(X0,X1),X0) | k3_xboole_0(X0,X1) = X0) )),
% 44.14/5.94    inference(resolution,[],[f266,f55])).
% 44.14/5.94  fof(f81637,plain,(
% 44.14/5.94    spl9_3 | ~spl9_76 | ~spl9_73),
% 44.14/5.94    inference(avatar_split_clause,[],[f80921,f78248,f81297,f103])).
% 44.14/5.94  fof(f80921,plain,(
% 44.14/5.94    ~r2_hidden(sK6(sK2,sK0),sK2) | sK0 = sK2 | ~spl9_73),
% 44.14/5.94    inference(superposition,[],[f374,f78250])).
% 44.14/5.94  fof(f374,plain,(
% 44.14/5.94    ( ! [X0,X1] : (~r2_hidden(sK6(k3_xboole_0(X0,X1),X0),k3_xboole_0(X0,X1)) | k3_xboole_0(X0,X1) = X0) )),
% 44.14/5.94    inference(resolution,[],[f272,f66])).
% 44.14/5.94  fof(f81581,plain,(
% 44.14/5.94    spl9_7 | spl9_78 | ~spl9_73),
% 44.14/5.94    inference(avatar_split_clause,[],[f80908,f78248,f81578,f174])).
% 44.14/5.94  fof(f80908,plain,(
% 44.14/5.94    r2_hidden(sK6(k1_xboole_0,sK2),sK0) | k1_xboole_0 = sK2 | ~spl9_73),
% 44.14/5.94    inference(superposition,[],[f153,f78250])).
% 44.14/5.94  fof(f81458,plain,(
% 44.14/5.94    spl9_58 | ~spl9_36 | ~spl9_73),
% 44.14/5.94    inference(avatar_split_clause,[],[f79712,f78248,f11051,f60570])).
% 44.14/5.94  fof(f60570,plain,(
% 44.14/5.94    spl9_58 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_58])])).
% 44.14/5.94  fof(f81305,plain,(
% 44.14/5.94    spl9_77 | ~spl9_75),
% 44.14/5.94    inference(avatar_split_clause,[],[f81295,f81290,f81302])).
% 44.14/5.94  fof(f81295,plain,(
% 44.14/5.94    r2_hidden(sK6(sK2,sK0),sK0) | ~spl9_75),
% 44.14/5.94    inference(resolution,[],[f81292,f65])).
% 44.14/5.94  fof(f81292,plain,(
% 44.14/5.94    r2_xboole_0(sK2,sK0) | ~spl9_75),
% 44.14/5.94    inference(avatar_component_clause,[],[f81290])).
% 44.14/5.94  fof(f81300,plain,(
% 44.14/5.94    ~spl9_76 | ~spl9_75),
% 44.14/5.94    inference(avatar_split_clause,[],[f81294,f81290,f81297])).
% 44.14/5.94  fof(f81294,plain,(
% 44.14/5.94    ~r2_hidden(sK6(sK2,sK0),sK2) | ~spl9_75),
% 44.14/5.94    inference(resolution,[],[f81292,f66])).
% 44.14/5.94  fof(f81293,plain,(
% 44.14/5.94    spl9_3 | spl9_75 | ~spl9_73),
% 44.14/5.94    inference(avatar_split_clause,[],[f80915,f78248,f81290,f103])).
% 44.14/5.94  fof(f80915,plain,(
% 44.14/5.94    r2_xboole_0(sK2,sK0) | sK0 = sK2 | ~spl9_73),
% 44.14/5.94    inference(superposition,[],[f272,f78250])).
% 44.14/5.94  fof(f81066,plain,(
% 44.14/5.94    spl9_74 | ~spl9_73),
% 44.14/5.94    inference(avatar_split_clause,[],[f80916,f78248,f78255])).
% 44.14/5.94  fof(f78255,plain,(
% 44.14/5.94    spl9_74 <=> sK2 = k3_xboole_0(sK2,sK0)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_74])])).
% 44.14/5.94  fof(f80916,plain,(
% 44.14/5.94    sK2 = k3_xboole_0(sK2,sK0) | ~spl9_73),
% 44.14/5.94    inference(superposition,[],[f273,f78250])).
% 44.14/5.94  fof(f81063,plain,(
% 44.14/5.94    spl9_71 | ~spl9_74),
% 44.14/5.94    inference(avatar_split_clause,[],[f78296,f78255,f78240])).
% 44.14/5.94  fof(f78240,plain,(
% 44.14/5.94    spl9_71 <=> r1_tarski(sK2,sK0)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_71])])).
% 44.14/5.94  fof(f78296,plain,(
% 44.14/5.94    r1_tarski(sK2,sK0) | ~spl9_74),
% 44.14/5.94    inference(superposition,[],[f261,f78257])).
% 44.14/5.94  fof(f78257,plain,(
% 44.14/5.94    sK2 = k3_xboole_0(sK2,sK0) | ~spl9_74),
% 44.14/5.94    inference(avatar_component_clause,[],[f78255])).
% 44.14/5.94  fof(f81049,plain,(
% 44.14/5.94    spl9_71 | ~spl9_73),
% 44.14/5.94    inference(avatar_split_clause,[],[f80914,f78248,f78240])).
% 44.14/5.94  fof(f80914,plain,(
% 44.14/5.94    r1_tarski(sK2,sK0) | ~spl9_73),
% 44.14/5.94    inference(superposition,[],[f266,f78250])).
% 44.14/5.94  fof(f79678,plain,(
% 44.14/5.94    ~spl9_72),
% 44.14/5.94    inference(avatar_contradiction_clause,[],[f79668])).
% 44.14/5.94  fof(f79668,plain,(
% 44.14/5.94    $false | ~spl9_72),
% 44.14/5.94    inference(resolution,[],[f78246,f123])).
% 44.14/5.94  fof(f78246,plain,(
% 44.14/5.94    r2_hidden(sK4(sK2,sK0),k1_xboole_0) | ~spl9_72),
% 44.14/5.94    inference(avatar_component_clause,[],[f78244])).
% 44.14/5.94  fof(f78244,plain,(
% 44.14/5.94    spl9_72 <=> r2_hidden(sK4(sK2,sK0),k1_xboole_0)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_72])])).
% 44.14/5.94  fof(f79656,plain,(
% 44.14/5.94    spl9_73 | ~spl9_74),
% 44.14/5.94    inference(avatar_split_clause,[],[f78259,f78255,f78248])).
% 44.14/5.94  fof(f78259,plain,(
% 44.14/5.94    sK2 = k3_xboole_0(sK0,sK2) | ~spl9_74),
% 44.14/5.94    inference(superposition,[],[f78257,f53])).
% 44.14/5.94  fof(f78258,plain,(
% 44.14/5.94    spl9_74 | ~spl9_71),
% 44.14/5.94    inference(avatar_split_clause,[],[f78253,f78240,f78255])).
% 44.14/5.94  fof(f78253,plain,(
% 44.14/5.94    sK2 = k3_xboole_0(sK2,sK0) | ~spl9_71),
% 44.14/5.94    inference(resolution,[],[f78242,f54])).
% 44.14/5.94  fof(f78242,plain,(
% 44.14/5.94    r1_tarski(sK2,sK0) | ~spl9_71),
% 44.14/5.94    inference(avatar_component_clause,[],[f78240])).
% 44.14/5.94  fof(f78251,plain,(
% 44.14/5.94    spl9_71 | spl9_72 | spl9_73 | ~spl9_22),
% 44.14/5.94    inference(avatar_split_clause,[],[f78033,f6922,f78248,f78244,f78240])).
% 44.14/5.94  fof(f6922,plain,(
% 44.14/5.94    spl9_22 <=> ! [X14] : k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X14,sK0))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 44.14/5.94  fof(f78033,plain,(
% 44.14/5.94    sK2 = k3_xboole_0(sK0,sK2) | r2_hidden(sK4(sK2,sK0),k1_xboole_0) | r1_tarski(sK2,sK0) | ~spl9_22),
% 44.14/5.94    inference(forward_demodulation,[],[f77939,f53])).
% 44.14/5.94  fof(f77939,plain,(
% 44.14/5.94    r2_hidden(sK4(sK2,sK0),k1_xboole_0) | r1_tarski(sK2,sK0) | sK2 = k3_xboole_0(sK2,sK0) | ~spl9_22),
% 44.14/5.94    inference(superposition,[],[f198,f77912])).
% 44.14/5.94  fof(f77912,plain,(
% 44.14/5.94    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(sK4(X1,sK0))) | k3_xboole_0(X1,sK0) = X1) ) | ~spl9_22),
% 44.14/5.94    inference(resolution,[],[f77819,f54])).
% 44.14/5.94  fof(f77819,plain,(
% 44.14/5.94    ( ! [X13] : (r1_tarski(X13,sK0) | k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(sK4(X13,sK0)))) ) | ~spl9_22),
% 44.14/5.94    inference(resolution,[],[f77725,f57])).
% 44.14/5.94  fof(f77725,plain,(
% 44.14/5.94    ( ! [X0] : (r2_hidden(X0,sK0) | k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(X0))) ) | ~spl9_22),
% 44.14/5.94    inference(resolution,[],[f46279,f2026])).
% 44.14/5.94  fof(f46279,plain,(
% 44.14/5.94    ( ! [X4,X5] : (~r2_hidden(X4,k4_xboole_0(X5,k1_xboole_0)) | r2_hidden(X4,sK0) | k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(X4))) ) | ~spl9_22),
% 44.14/5.94    inference(superposition,[],[f188,f46187])).
% 44.14/5.94  fof(f46187,plain,(
% 44.14/5.94    ( ! [X451] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X451),sK0) | k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(X451))) ) | ~spl9_22),
% 44.14/5.94    inference(superposition,[],[f6923,f41576])).
% 44.14/5.94  fof(f6923,plain,(
% 44.14/5.94    ( ! [X14] : (k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X14,sK0))) ) | ~spl9_22),
% 44.14/5.94    inference(avatar_component_clause,[],[f6922])).
% 44.14/5.94  fof(f198,plain,(
% 44.14/5.94    ( ! [X4,X3] : (r2_hidden(sK4(X3,X4),k3_xboole_0(X3,k1_tarski(sK4(X3,X4)))) | r1_tarski(X3,X4)) )),
% 44.14/5.94    inference(resolution,[],[f192,f56])).
% 44.14/5.94  fof(f77183,plain,(
% 44.14/5.94    spl9_70 | ~spl9_65),
% 44.14/5.94    inference(avatar_split_clause,[],[f69727,f69715,f77180])).
% 44.14/5.94  fof(f77180,plain,(
% 44.14/5.94    spl9_70 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))),k2_zfmisc_1(sK2,sK1))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_70])])).
% 44.14/5.94  fof(f69715,plain,(
% 44.14/5.94    spl9_65 <=> r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK2,sK1))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_65])])).
% 44.14/5.94  fof(f69727,plain,(
% 44.14/5.94    k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))),k2_zfmisc_1(sK2,sK1)) | ~spl9_65),
% 44.14/5.94    inference(resolution,[],[f69717,f26029])).
% 44.14/5.94  fof(f69717,plain,(
% 44.14/5.94    r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK2,sK1)) | ~spl9_65),
% 44.14/5.94    inference(avatar_component_clause,[],[f69715])).
% 44.14/5.94  fof(f76279,plain,(
% 44.14/5.94    spl9_69 | ~spl9_60),
% 44.14/5.94    inference(avatar_split_clause,[],[f69435,f60582,f76276])).
% 44.14/5.94  fof(f76276,plain,(
% 44.14/5.94    spl9_69 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))),k2_zfmisc_1(sK2,sK1))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_69])])).
% 44.14/5.94  fof(f60582,plain,(
% 44.14/5.94    spl9_60 <=> r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)),k2_zfmisc_1(sK2,sK1))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_60])])).
% 44.14/5.94  fof(f69435,plain,(
% 44.14/5.94    k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))),k2_zfmisc_1(sK2,sK1)) | ~spl9_60),
% 44.14/5.94    inference(resolution,[],[f60584,f26029])).
% 44.14/5.94  fof(f60584,plain,(
% 44.14/5.94    r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)),k2_zfmisc_1(sK2,sK1)) | ~spl9_60),
% 44.14/5.94    inference(avatar_component_clause,[],[f60582])).
% 44.14/5.94  fof(f76274,plain,(
% 44.14/5.94    spl9_68 | spl9_59),
% 44.14/5.94    inference(avatar_split_clause,[],[f69413,f60577,f76271])).
% 44.14/5.94  fof(f76271,plain,(
% 44.14/5.94    spl9_68 <=> k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k1_tarski(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_68])])).
% 44.14/5.94  fof(f69413,plain,(
% 44.14/5.94    k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k1_tarski(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)))) | spl9_59),
% 44.14/5.94    inference(resolution,[],[f60579,f1331])).
% 44.14/5.94  fof(f76269,plain,(
% 44.14/5.94    spl9_67 | spl9_59),
% 44.14/5.94    inference(avatar_split_clause,[],[f69400,f60577,f76266])).
% 44.14/5.94  fof(f76266,plain,(
% 44.14/5.94    spl9_67 <=> k1_xboole_0 = k3_xboole_0(k1_tarski(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))),k2_zfmisc_1(sK0,sK1))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_67])])).
% 44.14/5.94  fof(f69400,plain,(
% 44.14/5.94    k1_xboole_0 = k3_xboole_0(k1_tarski(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))),k2_zfmisc_1(sK0,sK1)) | spl9_59),
% 44.14/5.94    inference(resolution,[],[f60579,f963])).
% 44.14/5.94  fof(f75656,plain,(
% 44.14/5.94    spl9_8 | spl9_63 | ~spl9_34),
% 44.14/5.94    inference(avatar_split_clause,[],[f11038,f10903,f67300,f178])).
% 44.14/5.94  fof(f178,plain,(
% 44.14/5.94    spl9_8 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 44.14/5.94  fof(f67300,plain,(
% 44.14/5.94    spl9_63 <=> r2_hidden(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK2,sK1))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_63])])).
% 44.14/5.94  fof(f10903,plain,(
% 44.14/5.94    spl9_34 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).
% 44.14/5.94  fof(f11038,plain,(
% 44.14/5.94    r2_hidden(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK2,sK1)) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl9_34),
% 44.14/5.94    inference(resolution,[],[f10933,f151])).
% 44.14/5.94  fof(f10933,plain,(
% 44.14/5.94    ( ! [X20] : (~r2_hidden(X20,k2_zfmisc_1(sK0,sK1)) | r2_hidden(X20,k2_zfmisc_1(sK2,sK1))) ) | ~spl9_34),
% 44.14/5.94    inference(superposition,[],[f2967,f10905])).
% 44.14/5.94  fof(f10905,plain,(
% 44.14/5.94    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) | ~spl9_34),
% 44.14/5.94    inference(avatar_component_clause,[],[f10903])).
% 44.14/5.94  fof(f2967,plain,(
% 44.14/5.94    ( ! [X30,X33,X31,X32] : (~r2_hidden(X33,k2_zfmisc_1(X30,k3_xboole_0(X31,X32))) | r2_hidden(X33,k2_zfmisc_1(X30,X31))) )),
% 44.14/5.94    inference(superposition,[],[f90,f2034])).
% 44.14/5.94  fof(f2034,plain,(
% 44.14/5.94    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2))) )),
% 44.14/5.94    inference(superposition,[],[f79,f52])).
% 44.14/5.94  fof(f52,plain,(
% 44.14/5.94    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 44.14/5.94    inference(cnf_transformation,[],[f15])).
% 44.14/5.94  fof(f15,plain,(
% 44.14/5.94    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 44.14/5.94    inference(rectify,[],[f6])).
% 44.14/5.94  fof(f6,axiom,(
% 44.14/5.94    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 44.14/5.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 44.14/5.94  fof(f79,plain,(
% 44.14/5.94    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 44.14/5.94    inference(cnf_transformation,[],[f12])).
% 44.14/5.94  fof(f12,axiom,(
% 44.14/5.94    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 44.14/5.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 44.14/5.94  fof(f70369,plain,(
% 44.14/5.94    spl9_66 | ~spl9_49 | ~spl9_53),
% 44.14/5.94    inference(avatar_split_clause,[],[f55866,f53031,f52876,f70366])).
% 44.14/5.94  fof(f70366,plain,(
% 44.14/5.94    spl9_66 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),k2_zfmisc_1(sK0,sK1))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_66])])).
% 44.14/5.94  fof(f52876,plain,(
% 44.14/5.94    spl9_49 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).
% 44.14/5.94  fof(f53031,plain,(
% 44.14/5.94    spl9_53 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),k2_zfmisc_1(sK0,sK3))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_53])])).
% 44.14/5.94  fof(f55866,plain,(
% 44.14/5.94    k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),k2_zfmisc_1(sK0,sK1)) | (~spl9_49 | ~spl9_53)),
% 44.14/5.94    inference(backward_demodulation,[],[f53033,f52878])).
% 44.14/5.94  fof(f52878,plain,(
% 44.14/5.94    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3) | ~spl9_49),
% 44.14/5.94    inference(avatar_component_clause,[],[f52876])).
% 44.14/5.94  fof(f53033,plain,(
% 44.14/5.94    k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),k2_zfmisc_1(sK0,sK3)) | ~spl9_53),
% 44.14/5.94    inference(avatar_component_clause,[],[f53031])).
% 44.14/5.94  fof(f69718,plain,(
% 44.14/5.94    spl9_65 | ~spl9_34 | ~spl9_61),
% 44.14/5.94    inference(avatar_split_clause,[],[f69555,f62743,f10903,f69715])).
% 44.14/5.94  fof(f69555,plain,(
% 44.14/5.94    r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK2,sK1)) | (~spl9_34 | ~spl9_61)),
% 44.14/5.94    inference(resolution,[],[f62744,f10933])).
% 44.14/5.94  fof(f62744,plain,(
% 44.14/5.94    r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) | ~spl9_61),
% 44.14/5.94    inference(avatar_component_clause,[],[f62743])).
% 44.14/5.94  fof(f69624,plain,(
% 44.14/5.94    spl9_64 | ~spl9_63),
% 44.14/5.94    inference(avatar_split_clause,[],[f67312,f67300,f69621])).
% 44.14/5.94  fof(f69621,plain,(
% 44.14/5.94    spl9_64 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),k2_zfmisc_1(sK2,sK1))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_64])])).
% 44.14/5.94  fof(f67312,plain,(
% 44.14/5.94    k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),k2_zfmisc_1(sK2,sK1)) | ~spl9_63),
% 44.14/5.94    inference(resolution,[],[f67302,f26029])).
% 44.14/5.94  fof(f67302,plain,(
% 44.14/5.94    r2_hidden(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK2,sK1)) | ~spl9_63),
% 44.14/5.94    inference(avatar_component_clause,[],[f67300])).
% 44.14/5.94  fof(f69554,plain,(
% 44.14/5.94    spl9_61 | ~spl9_49 | ~spl9_50),
% 44.14/5.94    inference(avatar_split_clause,[],[f66741,f52883,f52876,f62743])).
% 44.14/5.94  fof(f52883,plain,(
% 44.14/5.94    spl9_50 <=> r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK0,sK1))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).
% 44.14/5.94  fof(f66741,plain,(
% 44.14/5.94    r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) | (~spl9_49 | ~spl9_50)),
% 44.14/5.94    inference(backward_demodulation,[],[f52884,f52878])).
% 44.14/5.94  fof(f52884,plain,(
% 44.14/5.94    r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK0,sK1)) | ~spl9_50),
% 44.14/5.94    inference(avatar_component_clause,[],[f52883])).
% 44.14/5.94  fof(f67303,plain,(
% 44.14/5.94    spl9_63 | ~spl9_34 | ~spl9_56),
% 44.14/5.94    inference(avatar_split_clause,[],[f67263,f56540,f10903,f67300])).
% 44.14/5.94  fof(f56540,plain,(
% 44.14/5.94    spl9_56 <=> r2_hidden(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).
% 44.14/5.94  fof(f67263,plain,(
% 44.14/5.94    r2_hidden(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK2,sK1)) | (~spl9_34 | ~spl9_56)),
% 44.14/5.94    inference(resolution,[],[f10933,f56542])).
% 44.14/5.94  fof(f56542,plain,(
% 44.14/5.94    r2_hidden(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) | ~spl9_56),
% 44.14/5.94    inference(avatar_component_clause,[],[f56540])).
% 44.14/5.94  fof(f66307,plain,(
% 44.14/5.94    spl9_62 | spl9_50),
% 44.14/5.94    inference(avatar_split_clause,[],[f52892,f52883,f66304])).
% 44.14/5.94  fof(f66304,plain,(
% 44.14/5.94    spl9_62 <=> k1_xboole_0 = k3_xboole_0(k1_tarski(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))),k2_zfmisc_1(sK0,sK1))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).
% 44.14/5.94  fof(f52892,plain,(
% 44.14/5.94    k1_xboole_0 = k3_xboole_0(k1_tarski(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))),k2_zfmisc_1(sK0,sK1)) | spl9_50),
% 44.14/5.94    inference(resolution,[],[f52885,f963])).
% 44.14/5.94  fof(f52885,plain,(
% 44.14/5.94    ~r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK0,sK1)) | spl9_50),
% 44.14/5.94    inference(avatar_component_clause,[],[f52883])).
% 44.14/5.94  fof(f62746,plain,(
% 44.14/5.94    ~spl9_61 | ~spl9_58 | spl9_59),
% 44.14/5.94    inference(avatar_split_clause,[],[f60967,f60577,f60570,f62743])).
% 44.14/5.94  fof(f60967,plain,(
% 44.14/5.94    ~r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) | (~spl9_58 | spl9_59)),
% 44.14/5.94    inference(backward_demodulation,[],[f60579,f60572])).
% 44.14/5.94  fof(f60572,plain,(
% 44.14/5.94    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1) | ~spl9_58),
% 44.14/5.94    inference(avatar_component_clause,[],[f60570])).
% 44.14/5.94  fof(f60585,plain,(
% 44.14/5.94    spl9_60 | ~spl9_57),
% 44.14/5.94    inference(avatar_split_clause,[],[f60575,f60566,f60582])).
% 44.14/5.94  fof(f60566,plain,(
% 44.14/5.94    spl9_57 <=> r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_57])])).
% 44.14/5.94  fof(f60575,plain,(
% 44.14/5.94    r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)),k2_zfmisc_1(sK2,sK1)) | ~spl9_57),
% 44.14/5.94    inference(resolution,[],[f60568,f65])).
% 44.14/5.94  fof(f60568,plain,(
% 44.14/5.94    r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) | ~spl9_57),
% 44.14/5.94    inference(avatar_component_clause,[],[f60566])).
% 44.14/5.94  fof(f60580,plain,(
% 44.14/5.94    ~spl9_59 | ~spl9_57),
% 44.14/5.94    inference(avatar_split_clause,[],[f60574,f60566,f60577])).
% 44.14/5.94  fof(f60574,plain,(
% 44.14/5.94    ~r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)),k2_zfmisc_1(sK0,sK1)) | ~spl9_57),
% 44.14/5.94    inference(resolution,[],[f60568,f66])).
% 44.14/5.94  fof(f60573,plain,(
% 44.14/5.94    spl9_57 | spl9_58 | ~spl9_35),
% 44.14/5.94    inference(avatar_split_clause,[],[f11022,f11018,f60570,f60566])).
% 44.14/5.94  fof(f11018,plain,(
% 44.14/5.94    spl9_35 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).
% 44.14/5.94  fof(f11022,plain,(
% 44.14/5.94    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1) | r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) | ~spl9_35),
% 44.14/5.94    inference(resolution,[],[f11020,f55])).
% 44.14/5.94  fof(f11020,plain,(
% 44.14/5.94    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) | ~spl9_35),
% 44.14/5.94    inference(avatar_component_clause,[],[f11018])).
% 44.14/5.94  fof(f56543,plain,(
% 44.14/5.94    spl9_56 | ~spl9_49 | ~spl9_52),
% 44.14/5.94    inference(avatar_split_clause,[],[f55829,f52973,f52876,f56540])).
% 44.14/5.94  fof(f52973,plain,(
% 44.14/5.94    spl9_52 <=> r2_hidden(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK3))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).
% 44.14/5.94  fof(f55829,plain,(
% 44.14/5.94    r2_hidden(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) | (~spl9_49 | ~spl9_52)),
% 44.14/5.94    inference(backward_demodulation,[],[f52975,f52878])).
% 44.14/5.94  fof(f52975,plain,(
% 44.14/5.94    r2_hidden(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK3)) | ~spl9_52),
% 44.14/5.94    inference(avatar_component_clause,[],[f52973])).
% 44.14/5.94  fof(f56522,plain,(
% 44.14/5.94    ~spl9_55 | spl9_48 | ~spl9_49),
% 44.14/5.94    inference(avatar_split_clause,[],[f56308,f52876,f52872,f56519])).
% 44.14/5.94  fof(f56519,plain,(
% 44.14/5.94    spl9_55 <=> r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_55])])).
% 44.14/5.94  fof(f52872,plain,(
% 44.14/5.94    spl9_48 <=> r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).
% 44.14/5.94  fof(f56308,plain,(
% 44.14/5.94    ~r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) | (spl9_48 | ~spl9_49)),
% 44.14/5.94    inference(forward_demodulation,[],[f52873,f52878])).
% 44.14/5.94  fof(f52873,plain,(
% 44.14/5.94    ~r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) | spl9_48),
% 44.14/5.94    inference(avatar_component_clause,[],[f52872])).
% 44.14/5.94  fof(f55677,plain,(
% 44.14/5.94    spl9_54 | ~spl9_51),
% 44.14/5.94    inference(avatar_split_clause,[],[f52927,f52888,f55674])).
% 44.14/5.94  fof(f55674,plain,(
% 44.14/5.94    spl9_54 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))),k2_zfmisc_1(sK0,sK3))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).
% 44.14/5.94  fof(f52888,plain,(
% 44.14/5.94    spl9_51 <=> r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK0,sK3))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_51])])).
% 44.14/5.94  fof(f52927,plain,(
% 44.14/5.94    k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))),k2_zfmisc_1(sK0,sK3)) | ~spl9_51),
% 44.14/5.94    inference(resolution,[],[f52890,f26029])).
% 44.14/5.94  fof(f52890,plain,(
% 44.14/5.94    r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK0,sK3)) | ~spl9_51),
% 44.14/5.94    inference(avatar_component_clause,[],[f52888])).
% 44.14/5.94  fof(f53034,plain,(
% 44.14/5.94    spl9_53 | ~spl9_52),
% 44.14/5.94    inference(avatar_split_clause,[],[f52985,f52973,f53031])).
% 44.14/5.94  fof(f52985,plain,(
% 44.14/5.94    k1_xboole_0 = k4_xboole_0(k1_tarski(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),k2_zfmisc_1(sK0,sK3)) | ~spl9_52),
% 44.14/5.94    inference(resolution,[],[f52975,f26029])).
% 44.14/5.94  fof(f52976,plain,(
% 44.14/5.94    spl9_8 | spl9_52 | ~spl9_25),
% 44.14/5.94    inference(avatar_split_clause,[],[f7909,f7805,f52973,f178])).
% 44.14/5.94  fof(f7805,plain,(
% 44.14/5.94    spl9_25 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 44.14/5.94  fof(f7909,plain,(
% 44.14/5.94    r2_hidden(sK6(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK3)) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl9_25),
% 44.14/5.94    inference(resolution,[],[f7811,f151])).
% 44.14/5.94  fof(f7811,plain,(
% 44.14/5.94    ( ! [X1] : (~r2_hidden(X1,k2_zfmisc_1(sK0,sK1)) | r2_hidden(X1,k2_zfmisc_1(sK0,sK3))) ) | ~spl9_25),
% 44.14/5.94    inference(superposition,[],[f5452,f7807])).
% 44.14/5.94  fof(f7807,plain,(
% 44.14/5.94    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3) | ~spl9_25),
% 44.14/5.94    inference(avatar_component_clause,[],[f7805])).
% 44.14/5.94  fof(f5452,plain,(
% 44.14/5.94    ( ! [X43,X41,X42,X40] : (~r2_hidden(X43,k2_zfmisc_1(k3_xboole_0(X40,X42),X41)) | r2_hidden(X43,k2_zfmisc_1(X40,X41))) )),
% 44.14/5.94    inference(superposition,[],[f90,f2057])).
% 44.14/5.94  fof(f2057,plain,(
% 44.14/5.94    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0)) )),
% 44.14/5.94    inference(superposition,[],[f79,f52])).
% 44.14/5.94  fof(f52891,plain,(
% 44.14/5.94    spl9_51 | ~spl9_48),
% 44.14/5.94    inference(avatar_split_clause,[],[f52881,f52872,f52888])).
% 44.14/5.94  fof(f52881,plain,(
% 44.14/5.94    r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK0,sK3)) | ~spl9_48),
% 44.14/5.94    inference(resolution,[],[f52874,f65])).
% 44.14/5.94  fof(f52874,plain,(
% 44.14/5.94    r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) | ~spl9_48),
% 44.14/5.94    inference(avatar_component_clause,[],[f52872])).
% 44.14/5.94  fof(f52886,plain,(
% 44.14/5.94    ~spl9_50 | ~spl9_48),
% 44.14/5.94    inference(avatar_split_clause,[],[f52880,f52872,f52883])).
% 44.14/5.94  fof(f52880,plain,(
% 44.14/5.94    ~r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK0,sK1)) | ~spl9_48),
% 44.14/5.94    inference(resolution,[],[f52874,f66])).
% 44.14/5.94  fof(f52879,plain,(
% 44.14/5.94    spl9_48 | spl9_49 | ~spl9_26),
% 44.14/5.94    inference(avatar_split_clause,[],[f7858,f7854,f52876,f52872])).
% 44.14/5.94  fof(f7854,plain,(
% 44.14/5.94    spl9_26 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 44.14/5.94  fof(f7858,plain,(
% 44.14/5.94    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3) | r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) | ~spl9_26),
% 44.14/5.94    inference(resolution,[],[f7856,f55])).
% 44.14/5.94  fof(f7856,plain,(
% 44.14/5.94    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) | ~spl9_26),
% 44.14/5.94    inference(avatar_component_clause,[],[f7854])).
% 44.14/5.94  fof(f15620,plain,(
% 44.14/5.94    spl9_6 | spl9_47 | ~spl9_5 | ~spl9_41),
% 44.14/5.94    inference(avatar_split_clause,[],[f14748,f11665,f112,f15618,f170])).
% 44.14/5.94  fof(f15618,plain,(
% 44.14/5.94    spl9_47 <=> ! [X55] : k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X55,k3_xboole_0(sK0,sK2)))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).
% 44.14/5.94  fof(f112,plain,(
% 44.14/5.94    spl9_5 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 44.14/5.94  fof(f11665,plain,(
% 44.14/5.94    spl9_41 <=> ! [X14] : k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X14,k3_xboole_0(sK0,sK2)))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).
% 44.14/5.94  fof(f14748,plain,(
% 44.14/5.94    ( ! [X55] : (k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X55,k3_xboole_0(sK0,sK2))) | k1_xboole_0 = sK3) ) | (~spl9_5 | ~spl9_41)),
% 44.14/5.94    inference(trivial_inequality_removal,[],[f14722])).
% 44.14/5.94  fof(f14722,plain,(
% 44.14/5.94    ( ! [X55] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X55,k3_xboole_0(sK0,sK2))) | k1_xboole_0 = sK3) ) | (~spl9_5 | ~spl9_41)),
% 44.14/5.94    inference(superposition,[],[f62,f14663])).
% 44.14/5.94  fof(f14663,plain,(
% 44.14/5.94    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(X3,k3_xboole_0(sK0,sK2))),sK3)) ) | (~spl9_5 | ~spl9_41)),
% 44.14/5.94    inference(forward_demodulation,[],[f14605,f53])).
% 44.14/5.94  fof(f14605,plain,(
% 44.14/5.94    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(k4_xboole_0(X3,k3_xboole_0(sK0,sK2)),sK2),sK3)) ) | (~spl9_5 | ~spl9_41)),
% 44.14/5.94    inference(superposition,[],[f11727,f7695])).
% 44.14/5.94  fof(f7695,plain,(
% 44.14/5.94    ( ! [X4] : (k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X4,sK3)) = k2_zfmisc_1(k3_xboole_0(X4,sK2),sK3)) ) | ~spl9_5),
% 44.14/5.94    inference(superposition,[],[f5416,f53])).
% 44.14/5.94  fof(f5416,plain,(
% 44.14/5.94    ( ! [X9] : (k2_zfmisc_1(k3_xboole_0(X9,sK2),sK3) = k3_xboole_0(k2_zfmisc_1(X9,sK3),k2_zfmisc_1(sK0,sK1))) ) | ~spl9_5),
% 44.14/5.94    inference(superposition,[],[f2057,f114])).
% 44.14/5.94  fof(f114,plain,(
% 44.14/5.94    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) | ~spl9_5),
% 44.14/5.94    inference(avatar_component_clause,[],[f112])).
% 44.14/5.94  fof(f11727,plain,(
% 44.14/5.94    ( ! [X6,X4,X5] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,X5),k2_zfmisc_1(k4_xboole_0(X4,k3_xboole_0(sK0,sK2)),X6))) ) | ~spl9_41),
% 44.14/5.94    inference(forward_demodulation,[],[f11691,f84])).
% 44.14/5.94  fof(f84,plain,(
% 44.14/5.94    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 44.14/5.94    inference(equality_resolution,[],[f63])).
% 44.14/5.94  fof(f63,plain,(
% 44.14/5.94    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 44.14/5.94    inference(cnf_transformation,[],[f34])).
% 44.14/5.94  fof(f34,plain,(
% 44.14/5.94    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 44.14/5.94    inference(flattening,[],[f33])).
% 44.14/5.94  fof(f33,plain,(
% 44.14/5.94    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 44.14/5.94    inference(nnf_transformation,[],[f11])).
% 44.14/5.94  fof(f11,axiom,(
% 44.14/5.94    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 44.14/5.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 44.14/5.94  fof(f11691,plain,(
% 44.14/5.94    ( ! [X6,X4,X5] : (k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X5,X6)) = k3_xboole_0(k2_zfmisc_1(sK0,X5),k2_zfmisc_1(k4_xboole_0(X4,k3_xboole_0(sK0,sK2)),X6))) ) | ~spl9_41),
% 44.14/5.94    inference(superposition,[],[f79,f11666])).
% 44.14/5.94  fof(f11666,plain,(
% 44.14/5.94    ( ! [X14] : (k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X14,k3_xboole_0(sK0,sK2)))) ) | ~spl9_41),
% 44.14/5.94    inference(avatar_component_clause,[],[f11665])).
% 44.14/5.94  fof(f62,plain,(
% 44.14/5.94    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 44.14/5.94    inference(cnf_transformation,[],[f34])).
% 44.14/5.94  fof(f15093,plain,(
% 44.14/5.94    spl9_46 | spl9_7 | ~spl9_5 | ~spl9_27),
% 44.14/5.94    inference(avatar_split_clause,[],[f13202,f7861,f112,f174,f15091])).
% 44.14/5.94  fof(f15091,plain,(
% 44.14/5.94    spl9_46 <=> ! [X54] : k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X54,k3_xboole_0(sK1,sK3)))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).
% 44.14/5.94  fof(f7861,plain,(
% 44.14/5.94    spl9_27 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).
% 44.14/5.94  fof(f13202,plain,(
% 44.14/5.94    ( ! [X54] : (k1_xboole_0 = sK2 | k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X54,k3_xboole_0(sK1,sK3)))) ) | (~spl9_5 | ~spl9_27)),
% 44.14/5.94    inference(trivial_inequality_removal,[],[f13177])).
% 44.14/5.94  fof(f13177,plain,(
% 44.14/5.94    ( ! [X54] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X54,k3_xboole_0(sK1,sK3)))) ) | (~spl9_5 | ~spl9_27)),
% 44.14/5.94    inference(superposition,[],[f62,f13121])).
% 44.14/5.94  fof(f13121,plain,(
% 44.14/5.94    ( ! [X9] : (k1_xboole_0 = k2_zfmisc_1(sK2,k3_xboole_0(sK3,k4_xboole_0(X9,k3_xboole_0(sK1,sK3))))) ) | (~spl9_5 | ~spl9_27)),
% 44.14/5.94    inference(forward_demodulation,[],[f13070,f53])).
% 44.14/5.94  fof(f13070,plain,(
% 44.14/5.94    ( ! [X9] : (k1_xboole_0 = k2_zfmisc_1(sK2,k3_xboole_0(k4_xboole_0(X9,k3_xboole_0(sK1,sK3)),sK3))) ) | (~spl9_5 | ~spl9_27)),
% 44.14/5.94    inference(superposition,[],[f7877,f4824])).
% 44.14/5.94  fof(f4824,plain,(
% 44.14/5.94    ( ! [X3] : (k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X3)) = k2_zfmisc_1(sK2,k3_xboole_0(X3,sK3))) ) | ~spl9_5),
% 44.14/5.94    inference(superposition,[],[f2949,f53])).
% 44.14/5.94  fof(f2949,plain,(
% 44.14/5.94    ( ! [X9] : (k2_zfmisc_1(sK2,k3_xboole_0(X9,sK3)) = k3_xboole_0(k2_zfmisc_1(sK2,X9),k2_zfmisc_1(sK0,sK1))) ) | ~spl9_5),
% 44.14/5.94    inference(superposition,[],[f2034,f114])).
% 44.14/5.94  fof(f7877,plain,(
% 44.14/5.94    ( ! [X12,X13] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X12,k4_xboole_0(X13,k3_xboole_0(sK1,sK3))))) ) | ~spl9_27),
% 44.14/5.94    inference(superposition,[],[f2103,f7863])).
% 44.14/5.94  fof(f7863,plain,(
% 44.14/5.94    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) | ~spl9_27),
% 44.14/5.94    inference(avatar_component_clause,[],[f7861])).
% 44.14/5.94  fof(f2103,plain,(
% 44.14/5.94    ( ! [X26,X24,X23,X25] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X25,X23),k2_zfmisc_1(X26,k4_xboole_0(X24,X23)))) )),
% 44.14/5.94    inference(forward_demodulation,[],[f2063,f83])).
% 44.14/5.94  fof(f83,plain,(
% 44.14/5.94    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 44.14/5.94    inference(equality_resolution,[],[f64])).
% 44.14/5.94  fof(f64,plain,(
% 44.14/5.94    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 44.14/5.94    inference(cnf_transformation,[],[f34])).
% 44.14/5.94  fof(f2063,plain,(
% 44.14/5.94    ( ! [X26,X24,X23,X25] : (k3_xboole_0(k2_zfmisc_1(X25,X23),k2_zfmisc_1(X26,k4_xboole_0(X24,X23))) = k2_zfmisc_1(k3_xboole_0(X25,X26),k1_xboole_0)) )),
% 44.14/5.94    inference(superposition,[],[f79,f713])).
% 44.14/5.94  fof(f713,plain,(
% 44.14/5.94    ( ! [X24,X25] : (k1_xboole_0 = k3_xboole_0(X24,k4_xboole_0(X25,X24))) )),
% 44.14/5.94    inference(superposition,[],[f695,f126])).
% 44.14/5.94  fof(f695,plain,(
% 44.14/5.94    ( ! [X4,X5,X3] : (k3_xboole_0(X3,k4_xboole_0(X4,X3)) = k3_xboole_0(k3_xboole_0(X3,k4_xboole_0(X4,X3)),X5)) )),
% 44.14/5.94    inference(resolution,[],[f693,f54])).
% 44.14/5.94  fof(f693,plain,(
% 44.14/5.94    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X1,k4_xboole_0(X0,X1)),X2)) )),
% 44.14/5.94    inference(forward_demodulation,[],[f692,f53])).
% 44.14/5.94  fof(f692,plain,(
% 44.14/5.94    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(k4_xboole_0(X0,X1),X1),X2)) )),
% 44.14/5.94    inference(duplicate_literal_removal,[],[f675])).
% 44.14/5.94  fof(f675,plain,(
% 44.14/5.94    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(k4_xboole_0(X0,X1),X1),X2) | r1_tarski(k3_xboole_0(k4_xboole_0(X0,X1),X1),X2)) )),
% 44.14/5.94    inference(resolution,[],[f248,f142])).
% 44.14/5.94  fof(f142,plain,(
% 44.14/5.94    ( ! [X2,X0,X1] : (r2_hidden(sK4(k3_xboole_0(X0,X1),X2),X0) | r1_tarski(k3_xboole_0(X0,X1),X2)) )),
% 44.14/5.94    inference(resolution,[],[f90,f56])).
% 44.14/5.94  fof(f248,plain,(
% 44.14/5.94    ( ! [X19,X17,X18,X16] : (~r2_hidden(sK4(k3_xboole_0(X16,X17),X18),k4_xboole_0(X19,X17)) | r1_tarski(k3_xboole_0(X16,X17),X18)) )),
% 44.14/5.94    inference(resolution,[],[f136,f86])).
% 44.14/5.94  fof(f14938,plain,(
% 44.14/5.94    spl9_6 | spl9_45 | ~spl9_44),
% 44.14/5.94    inference(avatar_split_clause,[],[f14887,f14836,f14935,f170])).
% 44.14/5.94  fof(f14935,plain,(
% 44.14/5.94    spl9_45 <=> k1_xboole_0 = k4_xboole_0(sK2,k3_xboole_0(sK0,sK2))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_45])])).
% 44.14/5.94  fof(f14836,plain,(
% 44.14/5.94    spl9_44 <=> k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,k3_xboole_0(sK0,sK2)),sK3)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).
% 44.14/5.94  fof(f14887,plain,(
% 44.14/5.94    k1_xboole_0 = k4_xboole_0(sK2,k3_xboole_0(sK0,sK2)) | k1_xboole_0 = sK3 | ~spl9_44),
% 44.14/5.94    inference(trivial_inequality_removal,[],[f14861])).
% 44.14/5.94  fof(f14861,plain,(
% 44.14/5.94    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(sK2,k3_xboole_0(sK0,sK2)) | k1_xboole_0 = sK3 | ~spl9_44),
% 44.14/5.94    inference(superposition,[],[f62,f14838])).
% 44.14/5.94  fof(f14838,plain,(
% 44.14/5.94    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,k3_xboole_0(sK0,sK2)),sK3) | ~spl9_44),
% 44.14/5.94    inference(avatar_component_clause,[],[f14836])).
% 44.14/5.94  fof(f14839,plain,(
% 44.14/5.94    spl9_44 | ~spl9_5 | ~spl9_41),
% 44.14/5.94    inference(avatar_split_clause,[],[f14686,f11665,f112,f14836])).
% 44.14/5.94  fof(f14686,plain,(
% 44.14/5.94    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,k3_xboole_0(sK0,sK2)),sK3) | (~spl9_5 | ~spl9_41)),
% 44.14/5.94    inference(superposition,[],[f14663,f226])).
% 44.14/5.94  fof(f13389,plain,(
% 44.14/5.94    spl9_43 | spl9_7 | ~spl9_42),
% 44.14/5.94    inference(avatar_split_clause,[],[f13338,f13289,f174,f13386])).
% 44.14/5.94  fof(f13289,plain,(
% 44.14/5.94    spl9_42 <=> k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,k3_xboole_0(sK1,sK3)))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).
% 44.14/5.94  fof(f13338,plain,(
% 44.14/5.94    k1_xboole_0 = sK2 | k1_xboole_0 = k4_xboole_0(sK3,k3_xboole_0(sK1,sK3)) | ~spl9_42),
% 44.14/5.94    inference(trivial_inequality_removal,[],[f13313])).
% 44.14/5.94  fof(f13313,plain,(
% 44.14/5.94    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 = k4_xboole_0(sK3,k3_xboole_0(sK1,sK3)) | ~spl9_42),
% 44.14/5.94    inference(superposition,[],[f62,f13291])).
% 44.14/5.94  fof(f13291,plain,(
% 44.14/5.94    k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,k3_xboole_0(sK1,sK3))) | ~spl9_42),
% 44.14/5.94    inference(avatar_component_clause,[],[f13289])).
% 44.14/5.94  fof(f13292,plain,(
% 44.14/5.94    spl9_42 | ~spl9_5 | ~spl9_27),
% 44.14/5.94    inference(avatar_split_clause,[],[f13143,f7861,f112,f13289])).
% 44.14/5.94  fof(f13143,plain,(
% 44.14/5.94    k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,k3_xboole_0(sK1,sK3))) | (~spl9_5 | ~spl9_27)),
% 44.14/5.94    inference(superposition,[],[f13121,f226])).
% 44.14/5.94  fof(f11667,plain,(
% 44.14/5.94    spl9_2 | spl9_41 | ~spl9_36),
% 44.14/5.94    inference(avatar_split_clause,[],[f11401,f11051,f11665,f98])).
% 44.14/5.94  fof(f11401,plain,(
% 44.14/5.94    ( ! [X14] : (k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X14,k3_xboole_0(sK0,sK2))) | k1_xboole_0 = sK1) ) | ~spl9_36),
% 44.14/5.94    inference(trivial_inequality_removal,[],[f11378])).
% 44.14/5.94  fof(f11378,plain,(
% 44.14/5.94    ( ! [X14] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X14,k3_xboole_0(sK0,sK2))) | k1_xboole_0 = sK1) ) | ~spl9_36),
% 44.14/5.94    inference(superposition,[],[f62,f11330])).
% 44.14/5.94  fof(f11330,plain,(
% 44.14/5.94    ( ! [X5] : (k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,k4_xboole_0(X5,k3_xboole_0(sK0,sK2))),sK1)) ) | ~spl9_36),
% 44.14/5.94    inference(forward_demodulation,[],[f11292,f84])).
% 44.14/5.94  fof(f11292,plain,(
% 44.14/5.94    ( ! [X5] : (k2_zfmisc_1(k1_xboole_0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,k4_xboole_0(X5,k3_xboole_0(sK0,sK2))),sK1)) ) | ~spl9_36),
% 44.14/5.94    inference(superposition,[],[f11092,f713])).
% 44.14/5.94  fof(f11092,plain,(
% 44.14/5.94    ( ! [X8] : (k2_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,sK2),X8),sK1) = k2_zfmisc_1(k3_xboole_0(sK0,X8),sK1)) ) | ~spl9_36),
% 44.14/5.94    inference(forward_demodulation,[],[f11066,f2057])).
% 44.14/5.94  fof(f11066,plain,(
% 44.14/5.94    ( ! [X8] : (k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X8,sK1)) = k2_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,sK2),X8),sK1)) ) | ~spl9_36),
% 44.14/5.94    inference(superposition,[],[f2057,f11053])).
% 44.14/5.94  fof(f11557,plain,(
% 44.14/5.94    spl9_2 | spl9_40 | ~spl9_39),
% 44.14/5.94    inference(avatar_split_clause,[],[f11473,f11440,f11554,f98])).
% 44.14/5.94  fof(f11554,plain,(
% 44.14/5.94    spl9_40 <=> k1_xboole_0 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).
% 44.14/5.94  fof(f11440,plain,(
% 44.14/5.94    spl9_39 <=> k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).
% 44.14/5.94  fof(f11473,plain,(
% 44.14/5.94    k1_xboole_0 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | k1_xboole_0 = sK1 | ~spl9_39),
% 44.14/5.94    inference(trivial_inequality_removal,[],[f11450])).
% 44.14/5.94  fof(f11450,plain,(
% 44.14/5.94    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | k1_xboole_0 = sK1 | ~spl9_39),
% 44.14/5.94    inference(superposition,[],[f62,f11442])).
% 44.14/5.94  fof(f11442,plain,(
% 44.14/5.94    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) | ~spl9_39),
% 44.14/5.94    inference(avatar_component_clause,[],[f11440])).
% 44.14/5.94  fof(f11443,plain,(
% 44.14/5.94    spl9_39 | ~spl9_36),
% 44.14/5.94    inference(avatar_split_clause,[],[f11369,f11051,f11440])).
% 44.14/5.94  fof(f11369,plain,(
% 44.14/5.94    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) | ~spl9_36),
% 44.14/5.94    inference(superposition,[],[f11330,f226])).
% 44.14/5.94  fof(f11176,plain,(
% 44.14/5.94    spl9_38 | ~spl9_37),
% 44.14/5.94    inference(avatar_split_clause,[],[f11145,f11116,f11173])).
% 44.14/5.94  fof(f11173,plain,(
% 44.14/5.94    spl9_38 <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK0,sK1))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).
% 44.14/5.94  fof(f11116,plain,(
% 44.14/5.94    spl9_37 <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).
% 44.14/5.94  fof(f11145,plain,(
% 44.14/5.94    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK0,sK1)) | ~spl9_37),
% 44.14/5.94    inference(superposition,[],[f289,f11118])).
% 44.14/5.94  fof(f11118,plain,(
% 44.14/5.94    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) | ~spl9_37),
% 44.14/5.94    inference(avatar_component_clause,[],[f11116])).
% 44.14/5.94  fof(f289,plain,(
% 44.14/5.94    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,k3_xboole_0(X2,X3))) )),
% 44.14/5.94    inference(superposition,[],[f264,f53])).
% 44.14/5.94  fof(f264,plain,(
% 44.14/5.94    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),X3)) )),
% 44.14/5.94    inference(resolution,[],[f261,f54])).
% 44.14/5.94  fof(f11119,plain,(
% 44.14/5.94    spl9_37 | ~spl9_35),
% 44.14/5.94    inference(avatar_split_clause,[],[f11023,f11018,f11116])).
% 44.14/5.94  fof(f11023,plain,(
% 44.14/5.94    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) | ~spl9_35),
% 44.14/5.94    inference(resolution,[],[f11020,f54])).
% 44.14/5.94  fof(f11054,plain,(
% 44.14/5.94    spl9_36 | ~spl9_5 | ~spl9_18 | ~spl9_33),
% 44.14/5.94    inference(avatar_split_clause,[],[f10819,f10216,f5988,f112,f11051])).
% 44.14/5.94  fof(f5988,plain,(
% 44.14/5.94    spl9_18 <=> k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 44.14/5.94  fof(f10216,plain,(
% 44.14/5.94    spl9_33 <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).
% 44.14/5.94  fof(f10819,plain,(
% 44.14/5.94    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) | (~spl9_5 | ~spl9_18 | ~spl9_33)),
% 44.14/5.94    inference(backward_demodulation,[],[f5990,f10818])).
% 44.14/5.94  fof(f10818,plain,(
% 44.14/5.94    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) | (~spl9_5 | ~spl9_33)),
% 44.14/5.94    inference(forward_demodulation,[],[f10817,f289])).
% 44.14/5.94  fof(f10817,plain,(
% 44.14/5.94    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK3,k3_xboole_0(sK1,sK3))) | (~spl9_5 | ~spl9_33)),
% 44.14/5.94    inference(forward_demodulation,[],[f10776,f53])).
% 44.14/5.94  fof(f10776,plain,(
% 44.14/5.94    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k3_xboole_0(k3_xboole_0(sK1,sK3),sK3)) | (~spl9_5 | ~spl9_33)),
% 44.14/5.94    inference(superposition,[],[f10218,f4824])).
% 44.14/5.94  fof(f10218,plain,(
% 44.14/5.94    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))) | ~spl9_33),
% 44.14/5.94    inference(avatar_component_clause,[],[f10216])).
% 44.14/5.94  fof(f5990,plain,(
% 44.14/5.94    k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) | ~spl9_18),
% 44.14/5.94    inference(avatar_component_clause,[],[f5988])).
% 44.14/5.94  fof(f11021,plain,(
% 44.14/5.94    spl9_35 | ~spl9_34),
% 44.14/5.94    inference(avatar_split_clause,[],[f10935,f10903,f11018])).
% 44.14/5.94  fof(f10935,plain,(
% 44.14/5.94    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) | ~spl9_34),
% 44.14/5.94    inference(superposition,[],[f2976,f10905])).
% 44.14/5.94  fof(f2976,plain,(
% 44.14/5.94    ( ! [X64,X62,X63] : (r1_tarski(k2_zfmisc_1(X62,k3_xboole_0(X63,X64)),k2_zfmisc_1(X62,X63))) )),
% 44.14/5.94    inference(superposition,[],[f266,f2034])).
% 44.14/5.94  fof(f10906,plain,(
% 44.14/5.94    spl9_34 | ~spl9_5 | ~spl9_33),
% 44.14/5.94    inference(avatar_split_clause,[],[f10818,f10216,f112,f10903])).
% 44.14/5.94  fof(f10219,plain,(
% 44.14/5.94    spl9_33 | ~spl9_19),
% 44.14/5.94    inference(avatar_split_clause,[],[f6287,f6282,f10216])).
% 44.14/5.94  fof(f6282,plain,(
% 44.14/5.94    spl9_19 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 44.14/5.94  fof(f6287,plain,(
% 44.14/5.94    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))) | ~spl9_19),
% 44.14/5.94    inference(resolution,[],[f6284,f54])).
% 44.14/5.94  fof(f6284,plain,(
% 44.14/5.94    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))) | ~spl9_19),
% 44.14/5.94    inference(avatar_component_clause,[],[f6282])).
% 44.14/5.94  fof(f9153,plain,(
% 44.14/5.94    spl9_32 | spl9_1 | ~spl9_27),
% 44.14/5.94    inference(avatar_split_clause,[],[f9014,f7861,f93,f9151])).
% 44.14/5.94  fof(f9151,plain,(
% 44.14/5.94    spl9_32 <=> ! [X15] : k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(X15,k3_xboole_0(sK1,sK3)))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).
% 44.14/5.94  fof(f9014,plain,(
% 44.14/5.94    ( ! [X15] : (k1_xboole_0 = sK0 | k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(X15,k3_xboole_0(sK1,sK3)))) ) | ~spl9_27),
% 44.14/5.94    inference(trivial_inequality_removal,[],[f8997])).
% 44.14/5.94  fof(f8997,plain,(
% 44.14/5.94    ( ! [X15] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(X15,k3_xboole_0(sK1,sK3)))) ) | ~spl9_27),
% 44.14/5.94    inference(superposition,[],[f62,f8956])).
% 44.14/5.94  fof(f8956,plain,(
% 44.14/5.94    ( ! [X5] : (k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(X5,k3_xboole_0(sK1,sK3))))) ) | ~spl9_27),
% 44.14/5.94    inference(forward_demodulation,[],[f8923,f83])).
% 44.14/5.94  fof(f8923,plain,(
% 44.14/5.94    ( ! [X5] : (k2_zfmisc_1(sK0,k1_xboole_0) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(X5,k3_xboole_0(sK1,sK3))))) ) | ~spl9_27),
% 44.14/5.94    inference(superposition,[],[f7886,f713])).
% 44.14/5.94  fof(f7886,plain,(
% 44.14/5.94    ( ! [X6] : (k2_zfmisc_1(sK0,k3_xboole_0(k3_xboole_0(sK1,sK3),X6)) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,X6))) ) | ~spl9_27),
% 44.14/5.94    inference(forward_demodulation,[],[f7872,f2034])).
% 44.14/5.94  fof(f7872,plain,(
% 44.14/5.94    ( ! [X6] : (k2_zfmisc_1(sK0,k3_xboole_0(k3_xboole_0(sK1,sK3),X6)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,X6))) ) | ~spl9_27),
% 44.14/5.94    inference(superposition,[],[f2034,f7863])).
% 44.14/5.94  fof(f9092,plain,(
% 44.14/5.94    spl9_31 | spl9_1 | ~spl9_30),
% 44.14/5.94    inference(avatar_split_clause,[],[f9072,f9044,f93,f9089])).
% 44.14/5.94  fof(f9044,plain,(
% 44.14/5.94    spl9_30 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,k3_xboole_0(sK1,sK3)))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).
% 44.14/5.94  fof(f9072,plain,(
% 44.14/5.94    k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK1,k3_xboole_0(sK1,sK3)) | ~spl9_30),
% 44.14/5.94    inference(trivial_inequality_removal,[],[f9055])).
% 44.14/5.94  fof(f9055,plain,(
% 44.14/5.94    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK1,k3_xboole_0(sK1,sK3)) | ~spl9_30),
% 44.14/5.94    inference(superposition,[],[f62,f9046])).
% 44.14/5.94  fof(f9046,plain,(
% 44.14/5.94    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,k3_xboole_0(sK1,sK3))) | ~spl9_30),
% 44.14/5.94    inference(avatar_component_clause,[],[f9044])).
% 44.14/5.94  fof(f9047,plain,(
% 44.14/5.94    spl9_30 | ~spl9_27),
% 44.14/5.94    inference(avatar_split_clause,[],[f8987,f7861,f9044])).
% 44.14/5.94  fof(f8987,plain,(
% 44.14/5.94    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,k3_xboole_0(sK1,sK3))) | ~spl9_27),
% 44.14/5.94    inference(superposition,[],[f8956,f226])).
% 44.14/5.94  fof(f7979,plain,(
% 44.14/5.94    spl9_29 | ~spl9_28),
% 44.14/5.94    inference(avatar_split_clause,[],[f7955,f7932,f7976])).
% 44.14/5.94  fof(f7976,plain,(
% 44.14/5.94    spl9_29 <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK1))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).
% 44.14/5.94  fof(f7932,plain,(
% 44.14/5.94    spl9_28 <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).
% 44.14/5.94  fof(f7955,plain,(
% 44.14/5.94    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK1)) | ~spl9_28),
% 44.14/5.94    inference(superposition,[],[f289,f7934])).
% 44.14/5.94  fof(f7934,plain,(
% 44.14/5.94    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) | ~spl9_28),
% 44.14/5.94    inference(avatar_component_clause,[],[f7932])).
% 44.14/5.94  fof(f7935,plain,(
% 44.14/5.94    spl9_28 | ~spl9_26),
% 44.14/5.94    inference(avatar_split_clause,[],[f7859,f7854,f7932])).
% 44.14/5.94  fof(f7859,plain,(
% 44.14/5.94    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) | ~spl9_26),
% 44.14/5.94    inference(resolution,[],[f7856,f54])).
% 44.14/5.94  fof(f7864,plain,(
% 44.14/5.94    spl9_27 | ~spl9_5 | ~spl9_23),
% 44.14/5.94    inference(avatar_split_clause,[],[f7740,f6992,f112,f7861])).
% 44.14/5.94  fof(f6992,plain,(
% 44.14/5.94    spl9_23 <=> k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 44.14/5.94  fof(f7740,plain,(
% 44.14/5.94    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) | (~spl9_5 | ~spl9_23)),
% 44.14/5.94    inference(forward_demodulation,[],[f7739,f114])).
% 44.14/5.94  fof(f7739,plain,(
% 44.14/5.94    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) | (~spl9_5 | ~spl9_23)),
% 44.14/5.94    inference(forward_demodulation,[],[f7738,f52])).
% 44.14/5.94  fof(f7738,plain,(
% 44.14/5.94    k2_zfmisc_1(k3_xboole_0(sK2,sK2),sK3) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) | (~spl9_5 | ~spl9_23)),
% 44.14/5.94    inference(forward_demodulation,[],[f7737,f2978])).
% 44.14/5.94  fof(f2978,plain,(
% 44.14/5.94    ( ! [X70,X68,X69] : (k2_zfmisc_1(X68,k3_xboole_0(X69,X70)) = k3_xboole_0(k2_zfmisc_1(X68,k3_xboole_0(X69,X70)),k2_zfmisc_1(X68,X69))) )),
% 44.14/5.94    inference(superposition,[],[f273,f2034])).
% 44.14/5.94  fof(f7737,plain,(
% 44.14/5.94    k2_zfmisc_1(k3_xboole_0(sK2,sK2),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) | (~spl9_5 | ~spl9_23)),
% 44.14/5.94    inference(forward_demodulation,[],[f7687,f7029])).
% 44.14/5.94  fof(f7029,plain,(
% 44.14/5.94    ( ! [X8] : (k2_zfmisc_1(k3_xboole_0(sK2,X8),sK3) = k2_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,sK2),X8),sK3)) ) | (~spl9_5 | ~spl9_23)),
% 44.14/5.94    inference(forward_demodulation,[],[f7028,f5410])).
% 44.14/5.94  fof(f5410,plain,(
% 44.14/5.94    ( ! [X9] : (k2_zfmisc_1(k3_xboole_0(sK2,X9),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X9,sK3))) ) | ~spl9_5),
% 44.14/5.94    inference(superposition,[],[f2057,f114])).
% 44.14/5.94  fof(f7028,plain,(
% 44.14/5.94    ( ! [X8] : (k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X8,sK3)) = k2_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,sK2),X8),sK3)) ) | ~spl9_23),
% 44.14/5.94    inference(forward_demodulation,[],[f7007,f2106])).
% 44.14/5.94  fof(f2106,plain,(
% 44.14/5.94    ( ! [X30,X33,X31,X32] : (k3_xboole_0(k2_zfmisc_1(X32,k3_xboole_0(X30,X31)),k2_zfmisc_1(X33,X31)) = k3_xboole_0(k2_zfmisc_1(X32,X30),k2_zfmisc_1(X33,X31))) )),
% 44.14/5.94    inference(forward_demodulation,[],[f2065,f79])).
% 44.14/5.94  fof(f2065,plain,(
% 44.14/5.94    ( ! [X30,X33,X31,X32] : (k3_xboole_0(k2_zfmisc_1(X32,k3_xboole_0(X30,X31)),k2_zfmisc_1(X33,X31)) = k2_zfmisc_1(k3_xboole_0(X32,X33),k3_xboole_0(X30,X31))) )),
% 44.14/5.94    inference(superposition,[],[f79,f264])).
% 44.14/5.94  fof(f7007,plain,(
% 44.14/5.94    ( ! [X8] : (k2_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,sK2),X8),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(X8,sK3))) ) | ~spl9_23),
% 44.14/5.94    inference(superposition,[],[f2057,f6994])).
% 44.14/5.94  fof(f6994,plain,(
% 44.14/5.94    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3) | ~spl9_23),
% 44.14/5.94    inference(avatar_component_clause,[],[f6992])).
% 44.14/5.94  fof(f7687,plain,(
% 44.14/5.94    k3_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,sK2),sK2),sK3) | (~spl9_5 | ~spl9_23)),
% 44.14/5.94    inference(superposition,[],[f5416,f6994])).
% 44.14/5.94  fof(f7857,plain,(
% 44.14/5.94    spl9_26 | ~spl9_25),
% 44.14/5.94    inference(avatar_split_clause,[],[f7813,f7805,f7854])).
% 44.14/5.94  fof(f7813,plain,(
% 44.14/5.94    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) | ~spl9_25),
% 44.14/5.94    inference(superposition,[],[f5461,f7807])).
% 44.14/5.94  fof(f5461,plain,(
% 44.14/5.94    ( ! [X74,X72,X73] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X72,X74),X73),k2_zfmisc_1(X72,X73))) )),
% 44.14/5.94    inference(superposition,[],[f266,f2057])).
% 44.14/5.94  fof(f7808,plain,(
% 44.14/5.94    spl9_25 | ~spl9_5 | ~spl9_23),
% 44.14/5.94    inference(avatar_split_clause,[],[f7741,f6992,f112,f7805])).
% 44.14/5.94  fof(f7741,plain,(
% 44.14/5.94    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3) | (~spl9_5 | ~spl9_23)),
% 44.14/5.94    inference(backward_demodulation,[],[f6994,f7740])).
% 44.14/5.94  fof(f7445,plain,(
% 44.14/5.94    spl9_24 | ~spl9_5 | ~spl9_23),
% 44.14/5.94    inference(avatar_split_clause,[],[f7433,f6992,f112,f7442])).
% 44.14/5.94  fof(f7442,plain,(
% 44.14/5.94    spl9_24 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 44.14/5.94  fof(f7433,plain,(
% 44.14/5.94    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) | (~spl9_5 | ~spl9_23)),
% 44.14/5.94    inference(superposition,[],[f7033,f52])).
% 44.14/5.94  fof(f7033,plain,(
% 44.14/5.94    ( ! [X18] : (r1_tarski(k2_zfmisc_1(sK0,k3_xboole_0(X18,sK1)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))) ) | (~spl9_5 | ~spl9_23)),
% 44.14/5.94    inference(forward_demodulation,[],[f7032,f2034])).
% 44.14/5.94  fof(f7032,plain,(
% 44.14/5.94    ( ! [X18] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(sK0,X18),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))) ) | (~spl9_5 | ~spl9_23)),
% 44.14/5.94    inference(forward_demodulation,[],[f7031,f114])).
% 44.14/5.94  fof(f7031,plain,(
% 44.14/5.94    ( ! [X18] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(sK0,X18),k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))) ) | ~spl9_23),
% 44.14/5.94    inference(forward_demodulation,[],[f7013,f79])).
% 44.14/5.94  fof(f7013,plain,(
% 44.14/5.94    ( ! [X18] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(X18,sK3)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))) ) | ~spl9_23),
% 44.14/5.94    inference(superposition,[],[f2973,f6994])).
% 44.14/5.94  fof(f2973,plain,(
% 44.14/5.94    ( ! [X54,X55,X53] : (r1_tarski(k2_zfmisc_1(X53,k3_xboole_0(X54,X55)),k2_zfmisc_1(X53,X55))) )),
% 44.14/5.94    inference(superposition,[],[f261,f2034])).
% 44.14/5.94  fof(f6995,plain,(
% 44.14/5.94    spl9_23 | ~spl9_5),
% 44.14/5.94    inference(avatar_split_clause,[],[f6674,f112,f6992])).
% 44.14/5.94  fof(f6674,plain,(
% 44.14/5.94    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3) | ~spl9_5),
% 44.14/5.94    inference(forward_demodulation,[],[f6620,f53])).
% 44.14/5.94  fof(f6620,plain,(
% 44.14/5.94    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK3) | ~spl9_5),
% 44.14/5.94    inference(superposition,[],[f5410,f2034])).
% 44.14/5.94  fof(f6924,plain,(
% 44.14/5.94    spl9_6 | spl9_22 | ~spl9_5),
% 44.14/5.94    inference(avatar_split_clause,[],[f6713,f112,f6922,f170])).
% 44.14/5.94  fof(f6713,plain,(
% 44.14/5.94    ( ! [X14] : (k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X14,sK0)) | k1_xboole_0 = sK3) ) | ~spl9_5),
% 44.14/5.94    inference(trivial_inequality_removal,[],[f6698])).
% 44.14/5.94  fof(f6698,plain,(
% 44.14/5.94    ( ! [X14] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X14,sK0)) | k1_xboole_0 = sK3) ) | ~spl9_5),
% 44.14/5.94    inference(superposition,[],[f62,f6623])).
% 44.14/5.94  fof(f6623,plain,(
% 44.14/5.94    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(X3,sK0)),sK3)) ) | ~spl9_5),
% 44.14/5.94    inference(superposition,[],[f5410,f2083])).
% 44.14/5.94  fof(f2083,plain,(
% 44.14/5.94    ( ! [X26,X24,X23,X25] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X23,X25),k2_zfmisc_1(k4_xboole_0(X24,X23),X26))) )),
% 44.14/5.94    inference(forward_demodulation,[],[f2040,f84])).
% 44.14/5.94  fof(f2040,plain,(
% 44.14/5.94    ( ! [X26,X24,X23,X25] : (k3_xboole_0(k2_zfmisc_1(X23,X25),k2_zfmisc_1(k4_xboole_0(X24,X23),X26)) = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X25,X26))) )),
% 44.14/5.94    inference(superposition,[],[f79,f713])).
% 44.14/5.94  fof(f6782,plain,(
% 44.14/5.94    spl9_6 | spl9_21 | ~spl9_20),
% 44.14/5.94    inference(avatar_split_clause,[],[f6766,f6739,f6779,f170])).
% 44.14/5.94  fof(f6779,plain,(
% 44.14/5.94    spl9_21 <=> k1_xboole_0 = k4_xboole_0(sK2,sK0)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 44.14/5.94  fof(f6739,plain,(
% 44.14/5.94    spl9_20 <=> k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 44.14/5.94  fof(f6766,plain,(
% 44.14/5.94    k1_xboole_0 = k4_xboole_0(sK2,sK0) | k1_xboole_0 = sK3 | ~spl9_20),
% 44.14/5.94    inference(trivial_inequality_removal,[],[f6751])).
% 44.14/5.94  fof(f6751,plain,(
% 44.14/5.94    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(sK2,sK0) | k1_xboole_0 = sK3 | ~spl9_20),
% 44.14/5.94    inference(superposition,[],[f62,f6741])).
% 44.14/5.94  fof(f6741,plain,(
% 44.14/5.94    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3) | ~spl9_20),
% 44.14/5.94    inference(avatar_component_clause,[],[f6739])).
% 44.14/5.94  fof(f6742,plain,(
% 44.14/5.94    spl9_20 | ~spl9_5),
% 44.14/5.94    inference(avatar_split_clause,[],[f6689,f112,f6739])).
% 44.14/5.94  fof(f6689,plain,(
% 44.14/5.94    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3) | ~spl9_5),
% 44.14/5.94    inference(superposition,[],[f6623,f226])).
% 44.14/5.94  fof(f6285,plain,(
% 44.14/5.94    spl9_19 | ~spl9_5 | ~spl9_18),
% 44.14/5.94    inference(avatar_split_clause,[],[f6273,f5988,f112,f6282])).
% 44.14/5.94  fof(f6273,plain,(
% 44.14/5.94    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))) | (~spl9_5 | ~spl9_18)),
% 44.14/5.94    inference(superposition,[],[f6021,f52])).
% 44.14/5.94  fof(f6021,plain,(
% 44.14/5.94    ( ! [X19] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X19,sK0),sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))) ) | (~spl9_5 | ~spl9_18)),
% 44.14/5.94    inference(forward_demodulation,[],[f6008,f6017])).
% 44.14/5.94  fof(f6017,plain,(
% 44.14/5.94    ( ! [X7] : (k2_zfmisc_1(k3_xboole_0(X7,k3_xboole_0(sK0,sK2)),sK1) = k2_zfmisc_1(k3_xboole_0(X7,sK0),sK1)) ) | (~spl9_5 | ~spl9_18)),
% 44.14/5.94    inference(forward_demodulation,[],[f6016,f2057])).
% 44.14/5.94  fof(f6016,plain,(
% 44.14/5.94    ( ! [X7] : (k2_zfmisc_1(k3_xboole_0(X7,k3_xboole_0(sK0,sK2)),sK1) = k3_xboole_0(k2_zfmisc_1(X7,sK1),k2_zfmisc_1(sK0,sK1))) ) | (~spl9_5 | ~spl9_18)),
% 44.14/5.94    inference(forward_demodulation,[],[f6015,f114])).
% 44.14/5.94  fof(f6015,plain,(
% 44.14/5.94    ( ! [X7] : (k2_zfmisc_1(k3_xboole_0(X7,k3_xboole_0(sK0,sK2)),sK1) = k3_xboole_0(k2_zfmisc_1(X7,sK1),k2_zfmisc_1(sK2,sK3))) ) | ~spl9_18),
% 44.14/5.94    inference(forward_demodulation,[],[f6000,f2102])).
% 44.14/5.94  fof(f2102,plain,(
% 44.14/5.94    ( ! [X17,X15,X18,X16] : (k3_xboole_0(k2_zfmisc_1(X17,X15),k2_zfmisc_1(X18,k3_xboole_0(X15,X16))) = k3_xboole_0(k2_zfmisc_1(X17,X15),k2_zfmisc_1(X18,X16))) )),
% 44.14/5.94    inference(forward_demodulation,[],[f2061,f79])).
% 44.14/5.94  fof(f2061,plain,(
% 44.14/5.94    ( ! [X17,X15,X18,X16] : (k3_xboole_0(k2_zfmisc_1(X17,X15),k2_zfmisc_1(X18,k3_xboole_0(X15,X16))) = k2_zfmisc_1(k3_xboole_0(X17,X18),k3_xboole_0(X15,X16))) )),
% 44.14/5.94    inference(superposition,[],[f79,f309])).
% 44.14/5.94  fof(f6000,plain,(
% 44.14/5.94    ( ! [X7] : (k2_zfmisc_1(k3_xboole_0(X7,k3_xboole_0(sK0,sK2)),sK1) = k3_xboole_0(k2_zfmisc_1(X7,sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))) ) | ~spl9_18),
% 44.14/5.94    inference(superposition,[],[f2057,f5990])).
% 44.14/5.94  fof(f6008,plain,(
% 44.14/5.94    ( ! [X19] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X19,k3_xboole_0(sK0,sK2)),sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))) ) | ~spl9_18),
% 44.14/5.94    inference(superposition,[],[f5458,f5990])).
% 44.14/5.94  fof(f5458,plain,(
% 44.14/5.94    ( ! [X64,X65,X63] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X63,X65),X64),k2_zfmisc_1(X65,X64))) )),
% 44.14/5.94    inference(superposition,[],[f261,f2057])).
% 44.14/5.94  fof(f5991,plain,(
% 44.14/5.94    spl9_18 | ~spl9_5),
% 44.14/5.94    inference(avatar_split_clause,[],[f5501,f112,f5988])).
% 44.14/5.94  fof(f5501,plain,(
% 44.14/5.94    k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) | ~spl9_5),
% 44.14/5.94    inference(forward_demodulation,[],[f5426,f53])).
% 44.14/5.94  fof(f5426,plain,(
% 44.14/5.94    k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK1) | ~spl9_5),
% 44.14/5.94    inference(superposition,[],[f2057,f2949])).
% 44.14/5.94  fof(f5926,plain,(
% 44.14/5.94    spl9_2 | spl9_17 | ~spl9_5),
% 44.14/5.94    inference(avatar_split_clause,[],[f5802,f112,f5924,f98])).
% 44.14/5.94  fof(f5802,plain,(
% 44.14/5.94    ( ! [X8] : (k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X8,sK2)) | k1_xboole_0 = sK1) ) | ~spl9_5),
% 44.14/5.94    inference(trivial_inequality_removal,[],[f5787])).
% 44.14/5.94  fof(f5787,plain,(
% 44.14/5.94    ( ! [X8] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X8,sK2)) | k1_xboole_0 = sK1) ) | ~spl9_5),
% 44.14/5.94    inference(superposition,[],[f62,f5422])).
% 44.14/5.94  fof(f5422,plain,(
% 44.14/5.94    ( ! [X11] : (k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,k4_xboole_0(X11,sK2)),sK1)) ) | ~spl9_5),
% 44.14/5.94    inference(superposition,[],[f2057,f2172])).
% 44.14/5.94  fof(f2172,plain,(
% 44.14/5.94    ( ! [X12,X13] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(X12,sK2),X13))) ) | ~spl9_5),
% 44.14/5.94    inference(superposition,[],[f2083,f114])).
% 44.14/5.94  fof(f5866,plain,(
% 44.14/5.94    spl9_2 | spl9_16 | ~spl9_15),
% 44.14/5.94    inference(avatar_split_clause,[],[f5851,f5825,f5863,f98])).
% 44.14/5.94  fof(f5825,plain,(
% 44.14/5.94    spl9_15 <=> k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 44.14/5.94  fof(f5851,plain,(
% 44.14/5.94    k1_xboole_0 = k4_xboole_0(sK0,sK2) | k1_xboole_0 = sK1 | ~spl9_15),
% 44.14/5.94    inference(trivial_inequality_removal,[],[f5836])).
% 44.14/5.94  fof(f5836,plain,(
% 44.14/5.94    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(sK0,sK2) | k1_xboole_0 = sK1 | ~spl9_15),
% 44.14/5.94    inference(superposition,[],[f62,f5827])).
% 44.14/5.94  fof(f5827,plain,(
% 44.14/5.94    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) | ~spl9_15),
% 44.14/5.94    inference(avatar_component_clause,[],[f5825])).
% 44.14/5.94  fof(f5828,plain,(
% 44.14/5.94    spl9_15 | ~spl9_5),
% 44.14/5.94    inference(avatar_split_clause,[],[f5782,f112,f5825])).
% 44.14/5.94  fof(f5782,plain,(
% 44.14/5.94    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) | ~spl9_5),
% 44.14/5.94    inference(superposition,[],[f5422,f226])).
% 44.14/5.94  fof(f4366,plain,(
% 44.14/5.94    spl9_6 | spl9_7 | ~spl9_8 | ~spl9_5),
% 44.14/5.94    inference(avatar_split_clause,[],[f4091,f112,f178,f174,f170])).
% 44.14/5.94  fof(f4091,plain,(
% 44.14/5.94    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~spl9_5),
% 44.14/5.94    inference(superposition,[],[f62,f114])).
% 44.14/5.94  fof(f4272,plain,(
% 44.14/5.94    spl9_2 | spl9_1 | ~spl9_8),
% 44.14/5.94    inference(avatar_split_clause,[],[f4266,f178,f93,f98])).
% 44.14/5.94  fof(f4266,plain,(
% 44.14/5.94    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl9_8),
% 44.14/5.94    inference(trivial_inequality_removal,[],[f4256])).
% 44.14/5.94  fof(f4256,plain,(
% 44.14/5.94    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl9_8),
% 44.14/5.94    inference(superposition,[],[f62,f179])).
% 44.14/5.94  fof(f179,plain,(
% 44.14/5.94    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl9_8),
% 44.14/5.94    inference(avatar_component_clause,[],[f178])).
% 44.14/5.94  fof(f4175,plain,(
% 44.14/5.94    spl9_14 | spl9_7 | ~spl9_5),
% 44.14/5.94    inference(avatar_split_clause,[],[f3874,f112,f174,f4173])).
% 44.14/5.94  fof(f4173,plain,(
% 44.14/5.94    spl9_14 <=> ! [X8] : k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X8,sK1))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 44.14/5.94  fof(f3874,plain,(
% 44.14/5.94    ( ! [X8] : (k1_xboole_0 = sK2 | k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X8,sK1))) ) | ~spl9_5),
% 44.14/5.94    inference(trivial_inequality_removal,[],[f3864])).
% 44.14/5.94  fof(f3864,plain,(
% 44.14/5.94    ( ! [X8] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X8,sK1))) ) | ~spl9_5),
% 44.14/5.94    inference(superposition,[],[f62,f3810])).
% 44.14/5.94  fof(f3810,plain,(
% 44.14/5.94    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(sK2,k3_xboole_0(sK3,k4_xboole_0(X3,sK1)))) ) | ~spl9_5),
% 44.14/5.94    inference(superposition,[],[f2945,f2103])).
% 44.14/5.94  fof(f2945,plain,(
% 44.14/5.94    ( ! [X9] : (k2_zfmisc_1(sK2,k3_xboole_0(sK3,X9)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X9))) ) | ~spl9_5),
% 44.14/5.94    inference(superposition,[],[f2034,f114])).
% 44.14/5.94  fof(f4047,plain,(
% 44.14/5.94    spl9_8 | ~spl9_5 | ~spl9_7),
% 44.14/5.94    inference(avatar_split_clause,[],[f3965,f174,f112,f178])).
% 44.14/5.94  fof(f3965,plain,(
% 44.14/5.94    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (~spl9_5 | ~spl9_7)),
% 44.14/5.94    inference(forward_demodulation,[],[f3926,f84])).
% 44.14/5.94  fof(f3926,plain,(
% 44.14/5.94    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,sK3) | (~spl9_5 | ~spl9_7)),
% 44.14/5.94    inference(backward_demodulation,[],[f114,f176])).
% 44.14/5.94  fof(f176,plain,(
% 44.14/5.94    k1_xboole_0 = sK2 | ~spl9_7),
% 44.14/5.94    inference(avatar_component_clause,[],[f174])).
% 44.14/5.94  fof(f3924,plain,(
% 44.14/5.94    spl9_13 | spl9_7 | ~spl9_12),
% 44.14/5.94    inference(avatar_split_clause,[],[f3913,f3893,f174,f3921])).
% 44.14/5.94  fof(f3893,plain,(
% 44.14/5.94    spl9_12 <=> k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 44.14/5.94  fof(f3913,plain,(
% 44.14/5.94    k1_xboole_0 = sK2 | k1_xboole_0 = k4_xboole_0(sK3,sK1) | ~spl9_12),
% 44.14/5.94    inference(trivial_inequality_removal,[],[f3903])).
% 44.14/5.94  fof(f3903,plain,(
% 44.14/5.94    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 = k4_xboole_0(sK3,sK1) | ~spl9_12),
% 44.14/5.94    inference(superposition,[],[f62,f3895])).
% 44.14/5.94  fof(f3895,plain,(
% 44.14/5.94    k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1)) | ~spl9_12),
% 44.14/5.94    inference(avatar_component_clause,[],[f3893])).
% 44.14/5.94  fof(f3896,plain,(
% 44.14/5.94    spl9_12 | ~spl9_5),
% 44.14/5.94    inference(avatar_split_clause,[],[f3857,f112,f3893])).
% 44.14/5.94  fof(f3857,plain,(
% 44.14/5.94    k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1)) | ~spl9_5),
% 44.14/5.94    inference(superposition,[],[f3810,f226])).
% 44.14/5.94  fof(f3323,plain,(
% 44.14/5.94    spl9_11 | spl9_1 | ~spl9_5),
% 44.14/5.94    inference(avatar_split_clause,[],[f3225,f112,f93,f3321])).
% 44.14/5.94  fof(f3225,plain,(
% 44.14/5.94    ( ! [X2] : (k1_xboole_0 = sK0 | k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(X2,sK3))) ) | ~spl9_5),
% 44.14/5.94    inference(trivial_inequality_removal,[],[f3215])).
% 44.14/5.94  fof(f3215,plain,(
% 44.14/5.94    ( ! [X2] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(X2,sK3))) ) | ~spl9_5),
% 44.14/5.94    inference(superposition,[],[f62,f2950])).
% 44.14/5.94  fof(f2950,plain,(
% 44.14/5.94    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(X0,sK3)))) ) | ~spl9_5),
% 44.14/5.94    inference(superposition,[],[f2034,f2256])).
% 44.14/5.94  fof(f2256,plain,(
% 44.14/5.94    ( ! [X12,X13] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X12,k4_xboole_0(X13,sK3)))) ) | ~spl9_5),
% 44.14/5.94    inference(superposition,[],[f2103,f114])).
% 44.14/5.94  fof(f3271,plain,(
% 44.14/5.94    spl9_10 | spl9_1 | ~spl9_9),
% 44.14/5.94    inference(avatar_split_clause,[],[f3261,f3242,f93,f3268])).
% 44.14/5.94  fof(f3242,plain,(
% 44.14/5.94    spl9_9 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))),
% 44.14/5.94    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 44.14/5.94  fof(f3261,plain,(
% 44.14/5.94    k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK1,sK3) | ~spl9_9),
% 44.14/5.94    inference(trivial_inequality_removal,[],[f3251])).
% 44.14/5.94  fof(f3251,plain,(
% 44.14/5.94    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK1,sK3) | ~spl9_9),
% 44.14/5.94    inference(superposition,[],[f62,f3244])).
% 44.14/5.94  fof(f3244,plain,(
% 44.14/5.94    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) | ~spl9_9),
% 44.14/5.94    inference(avatar_component_clause,[],[f3242])).
% 44.14/5.94  fof(f3245,plain,(
% 44.14/5.94    spl9_9 | ~spl9_5),
% 44.14/5.94    inference(avatar_split_clause,[],[f3212,f112,f3242])).
% 44.14/5.94  fof(f3212,plain,(
% 44.14/5.94    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) | ~spl9_5),
% 44.14/5.94    inference(superposition,[],[f2950,f226])).
% 44.14/5.94  fof(f181,plain,(
% 44.14/5.94    spl9_6 | spl9_7 | ~spl9_8 | ~spl9_5),
% 44.14/5.94    inference(avatar_split_clause,[],[f168,f112,f178,f174,f170])).
% 44.14/5.94  fof(f168,plain,(
% 44.14/5.94    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~spl9_5),
% 44.14/5.94    inference(superposition,[],[f62,f114])).
% 44.14/5.94  fof(f115,plain,(
% 44.14/5.94    spl9_5),
% 44.14/5.94    inference(avatar_split_clause,[],[f47,f112])).
% 44.14/5.94  fof(f47,plain,(
% 44.14/5.94    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 44.14/5.94    inference(cnf_transformation,[],[f26])).
% 44.14/5.94  fof(f26,plain,(
% 44.14/5.94    (sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 44.14/5.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f25])).
% 44.14/5.94  fof(f25,plain,(
% 44.14/5.94    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3))),
% 44.14/5.94    introduced(choice_axiom,[])).
% 44.14/5.94  fof(f19,plain,(
% 44.14/5.94    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 44.14/5.94    inference(flattening,[],[f18])).
% 44.14/5.94  fof(f18,plain,(
% 44.14/5.94    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 44.14/5.94    inference(ennf_transformation,[],[f14])).
% 44.14/5.94  fof(f14,negated_conjecture,(
% 44.14/5.94    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 44.14/5.94    inference(negated_conjecture,[],[f13])).
% 44.14/5.94  fof(f13,conjecture,(
% 44.14/5.94    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 44.14/5.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 44.14/5.94  fof(f110,plain,(
% 44.14/5.94    ~spl9_3 | ~spl9_4),
% 44.14/5.94    inference(avatar_split_clause,[],[f50,f107,f103])).
% 44.14/5.94  fof(f50,plain,(
% 44.14/5.94    sK1 != sK3 | sK0 != sK2),
% 44.14/5.94    inference(cnf_transformation,[],[f26])).
% 44.14/5.94  fof(f101,plain,(
% 44.14/5.94    ~spl9_2),
% 44.14/5.94    inference(avatar_split_clause,[],[f49,f98])).
% 44.14/5.94  fof(f49,plain,(
% 44.14/5.94    k1_xboole_0 != sK1),
% 44.14/5.94    inference(cnf_transformation,[],[f26])).
% 44.14/5.94  fof(f96,plain,(
% 44.14/5.94    ~spl9_1),
% 44.14/5.94    inference(avatar_split_clause,[],[f48,f93])).
% 44.14/5.94  fof(f48,plain,(
% 44.14/5.94    k1_xboole_0 != sK0),
% 44.14/5.94    inference(cnf_transformation,[],[f26])).
% 44.14/5.94  % SZS output end Proof for theBenchmark
% 44.14/5.94  % (27020)------------------------------
% 44.14/5.94  % (27020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 44.14/5.94  % (27020)Termination reason: Refutation
% 44.14/5.94  
% 44.14/5.94  % (27020)Memory used [KB]: 81747
% 44.14/5.94  % (27020)Time elapsed: 4.776 s
% 44.14/5.94  % (27020)------------------------------
% 44.14/5.94  % (27020)------------------------------
% 44.14/5.95  % (26748)Success in time 5.591 s
%------------------------------------------------------------------------------
