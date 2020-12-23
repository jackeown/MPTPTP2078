%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:23 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 315 expanded)
%              Number of leaves         :   40 ( 133 expanded)
%              Depth                    :    8
%              Number of atoms          :  408 ( 898 expanded)
%              Number of equality atoms :  109 ( 310 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1204,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f88,f93,f98,f103,f139,f226,f231,f248,f258,f287,f343,f356,f382,f412,f440,f452,f457,f463,f532,f819,f940,f951,f973,f980,f1041,f1190])).

fof(f1190,plain,
    ( ~ spl7_9
    | ~ spl7_85 ),
    inference(avatar_split_clause,[],[f1181,f1038,f136])).

fof(f136,plain,
    ( spl7_9
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f1038,plain,
    ( spl7_85
  <=> r2_hidden(k4_tarski(sK5(k2_zfmisc_1(sK0,sK1)),sK5(sK2)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_85])])).

fof(f1181,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl7_85 ),
    inference(resolution,[],[f1040,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f1040,plain,
    ( r2_hidden(k4_tarski(sK5(k2_zfmisc_1(sK0,sK1)),sK5(sK2)),o_0_0_xboole_0)
    | ~ spl7_85 ),
    inference(avatar_component_clause,[],[f1038])).

fof(f1041,plain,
    ( spl7_2
    | spl7_37
    | spl7_85
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f1007,f118,f1038,f366,f85])).

fof(f85,plain,
    ( spl7_2
  <=> o_0_0_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f366,plain,
    ( spl7_37
  <=> o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f118,plain,
    ( spl7_8
  <=> o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f1007,plain,
    ( r2_hidden(k4_tarski(sK5(k2_zfmisc_1(sK0,sK1)),sK5(sK2)),o_0_0_xboole_0)
    | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | o_0_0_xboole_0 = sK2
    | ~ spl7_8 ),
    inference(superposition,[],[f546,f120])).

fof(f120,plain,
    ( o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f118])).

fof(f546,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0),sK5(X1)),k2_zfmisc_1(X0,X1))
      | o_0_0_xboole_0 = X0
      | o_0_0_xboole_0 = X1 ) ),
    inference(resolution,[],[f170,f71])).

fof(f71,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f46,f42])).

fof(f42,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK5(X0),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(k4_tarski(sK5(X2),X0),k2_zfmisc_1(X2,X1))
      | o_0_0_xboole_0 = X2 ) ),
    inference(resolution,[],[f65,f71])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f980,plain,
    ( spl7_8
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f979,f112,f118])).

fof(f112,plain,
    ( spl7_7
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f979,plain,
    ( o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl7_7 ),
    inference(resolution,[],[f114,f105])).

fof(f105,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
      | o_0_0_xboole_0 = X1 ) ),
    inference(resolution,[],[f71,f43])).

fof(f114,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f112])).

fof(f973,plain,
    ( spl7_6
    | spl7_7
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f970,f100,f112,f108])).

fof(f108,plain,
    ( spl7_6
  <=> r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f100,plain,
    ( spl7_5
  <=> m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f970,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl7_5 ),
    inference(resolution,[],[f102,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f102,plain,
    ( m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f951,plain,
    ( ~ spl7_9
    | ~ spl7_76 ),
    inference(avatar_split_clause,[],[f942,f937,f136])).

fof(f937,plain,
    ( spl7_76
  <=> r2_hidden(k4_tarski(sK5(sK0),sK5(sK1)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_76])])).

fof(f942,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl7_76 ),
    inference(resolution,[],[f939,f43])).

fof(f939,plain,
    ( r2_hidden(k4_tarski(sK5(sK0),sK5(sK1)),o_0_0_xboole_0)
    | ~ spl7_76 ),
    inference(avatar_component_clause,[],[f937])).

fof(f940,plain,
    ( spl7_3
    | spl7_4
    | spl7_76
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f934,f366,f937,f95,f90])).

fof(f90,plain,
    ( spl7_3
  <=> o_0_0_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f95,plain,
    ( spl7_4
  <=> o_0_0_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f934,plain,
    ( r2_hidden(k4_tarski(sK5(sK0),sK5(sK1)),o_0_0_xboole_0)
    | o_0_0_xboole_0 = sK0
    | o_0_0_xboole_0 = sK1
    | ~ spl7_37 ),
    inference(superposition,[],[f546,f368])).

fof(f368,plain,
    ( o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f366])).

fof(f819,plain,
    ( ~ spl7_18
    | ~ spl7_25
    | ~ spl7_39
    | ~ spl7_50
    | ~ spl7_54 ),
    inference(avatar_split_clause,[],[f814,f461,f437,f375,f284,f241])).

fof(f241,plain,
    ( spl7_18
  <=> sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f284,plain,
    ( spl7_25
  <=> m1_subset_1(k2_mcart_1(sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f375,plain,
    ( spl7_39
  <=> k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f437,plain,
    ( spl7_50
  <=> m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f461,plain,
    ( spl7_54
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,sK1)
        | sK4 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),X0),X1)
        | ~ m1_subset_1(X1,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f814,plain,
    ( sK4 != k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | ~ spl7_25
    | ~ spl7_39
    | ~ spl7_50
    | ~ spl7_54 ),
    inference(resolution,[],[f805,f286])).

fof(f286,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f284])).

fof(f805,plain,
    ( ! [X9] :
        ( ~ m1_subset_1(X9,sK2)
        | sK4 != k4_tarski(k1_mcart_1(sK4),X9) )
    | ~ spl7_39
    | ~ spl7_50
    | ~ spl7_54 ),
    inference(forward_demodulation,[],[f800,f377])).

fof(f377,plain,
    ( k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f375])).

fof(f800,plain,
    ( ! [X9] :
        ( sK4 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))),X9)
        | ~ m1_subset_1(X9,sK2) )
    | ~ spl7_50
    | ~ spl7_54 ),
    inference(resolution,[],[f462,f439])).

fof(f439,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ spl7_50 ),
    inference(avatar_component_clause,[],[f437])).

fof(f462,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK1)
        | sK4 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),X0),X1)
        | ~ m1_subset_1(X1,sK2) )
    | ~ spl7_54 ),
    inference(avatar_component_clause,[],[f461])).

fof(f532,plain,(
    spl7_19 ),
    inference(avatar_contradiction_clause,[],[f531])).

fof(f531,plain,
    ( $false
    | spl7_19 ),
    inference(resolution,[],[f247,f47])).

fof(f47,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f247,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | spl7_19 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl7_19
  <=> v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f463,plain,
    ( spl7_53
    | spl7_54
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f458,f449,f461,f454])).

fof(f454,plain,
    ( spl7_53
  <=> sK3 = k1_mcart_1(k1_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f449,plain,
    ( spl7_52
  <=> m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f458,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ m1_subset_1(X1,sK2)
        | sK4 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),X0),X1)
        | sK3 = k1_mcart_1(k1_mcart_1(sK4)) )
    | ~ spl7_52 ),
    inference(resolution,[],[f451,f70])).

fof(f70,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK3 = X5 ) ),
    inference(definition_unfolding,[],[f36,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f36,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | k3_mcart_1(X5,X6,X7) != sK4
      | sK3 = X5 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k5_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X5
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k5_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X5
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X5 ) ) ) )
         => ( k5_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X5 ) ) ) )
       => ( k5_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_mcart_1)).

fof(f451,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ spl7_52 ),
    inference(avatar_component_clause,[],[f449])).

fof(f457,plain,
    ( ~ spl7_53
    | spl7_1
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f447,f340,f80,f454])).

fof(f80,plain,
    ( spl7_1
  <=> sK3 = k5_mcart_1(sK0,sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f340,plain,
    ( spl7_33
  <=> k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f447,plain,
    ( sK3 != k1_mcart_1(k1_mcart_1(sK4))
    | spl7_1
    | ~ spl7_33 ),
    inference(superposition,[],[f82,f342])).

fof(f342,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f340])).

fof(f82,plain,
    ( sK3 != k5_mcart_1(sK0,sK1,sK2,sK4)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f452,plain,
    ( spl7_52
    | ~ spl7_20
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f446,f340,f255,f449])).

fof(f255,plain,
    ( spl7_20
  <=> m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f446,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ spl7_20
    | ~ spl7_33 ),
    inference(backward_demodulation,[],[f257,f342])).

fof(f257,plain,
    ( m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f255])).

fof(f440,plain,
    ( spl7_50
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f417,f353,f437])).

fof(f353,plain,
    ( spl7_34
  <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f417,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ spl7_34 ),
    inference(resolution,[],[f355,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f355,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f353])).

fof(f412,plain,(
    spl7_40 ),
    inference(avatar_contradiction_clause,[],[f411])).

fof(f411,plain,
    ( $false
    | spl7_40 ),
    inference(resolution,[],[f381,f47])).

fof(f381,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl7_40 ),
    inference(avatar_component_clause,[],[f379])).

fof(f379,plain,
    ( spl7_40
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f382,plain,
    ( spl7_39
    | ~ spl7_40
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f349,f228,f379,f375])).

fof(f228,plain,
    ( spl7_15
  <=> r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f349,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))
    | ~ spl7_15 ),
    inference(resolution,[],[f230,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f230,plain,
    ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f228])).

fof(f356,plain,
    ( spl7_34
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f344,f228,f353])).

fof(f344,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ spl7_15 ),
    inference(resolution,[],[f230,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f343,plain,
    ( spl7_33
    | spl7_4
    | spl7_2
    | spl7_3
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f335,f100,f90,f85,f95,f340])).

fof(f335,plain,
    ( o_0_0_xboole_0 = sK1
    | o_0_0_xboole_0 = sK2
    | o_0_0_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | ~ spl7_5 ),
    inference(resolution,[],[f76,f102])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X0
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) ),
    inference(definition_unfolding,[],[f58,f42,f42,f42,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f287,plain,
    ( spl7_25
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f264,f223,f284])).

fof(f223,plain,
    ( spl7_14
  <=> r2_hidden(k2_mcart_1(sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f264,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ spl7_14 ),
    inference(resolution,[],[f225,f49])).

fof(f225,plain,
    ( r2_hidden(k2_mcart_1(sK4),sK2)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f223])).

fof(f258,plain,
    ( spl7_20
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f251,f100,f255])).

fof(f251,plain,
    ( m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0)
    | ~ spl7_5 ),
    inference(resolution,[],[f78,f102])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    inference(definition_unfolding,[],[f62,f55])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_mcart_1)).

fof(f248,plain,
    ( spl7_18
    | ~ spl7_19
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f219,f108,f245,f241])).

fof(f219,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | ~ spl7_6 ),
    inference(resolution,[],[f110,f48])).

fof(f110,plain,
    ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f108])).

fof(f231,plain,
    ( spl7_15
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f215,f108,f228])).

fof(f215,plain,
    ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl7_6 ),
    inference(resolution,[],[f110,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f226,plain,
    ( spl7_14
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f214,f108,f223])).

fof(f214,plain,
    ( r2_hidden(k2_mcart_1(sK4),sK2)
    | ~ spl7_6 ),
    inference(resolution,[],[f110,f57])).

fof(f139,plain,
    ( spl7_9
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f131,f118,f112,f136])).

fof(f131,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(backward_demodulation,[],[f114,f120])).

fof(f103,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f69,f100])).

fof(f69,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f37,f55])).

fof(f37,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f98,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f68,f95])).

fof(f68,plain,(
    o_0_0_xboole_0 != sK0 ),
    inference(definition_unfolding,[],[f38,f42])).

fof(f38,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f22])).

fof(f93,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f67,f90])).

fof(f67,plain,(
    o_0_0_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f39,f42])).

fof(f39,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f88,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f66,f85])).

fof(f66,plain,(
    o_0_0_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f40,f42])).

fof(f40,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f83,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f41,f80])).

fof(f41,plain,(
    sK3 != k5_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:51:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (7244)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.52  % (7236)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % (7224)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (7220)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (7221)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (7219)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (7226)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (7222)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (7234)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.29/0.53  % (7238)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.29/0.53  % (7216)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.29/0.53  % (7228)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.54  % (7216)Refutation not found, incomplete strategy% (7216)------------------------------
% 1.29/0.54  % (7216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (7220)Refutation not found, incomplete strategy% (7220)------------------------------
% 1.29/0.54  % (7220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (7224)Refutation not found, incomplete strategy% (7224)------------------------------
% 1.29/0.54  % (7224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (7239)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.29/0.54  % (7236)Refutation not found, incomplete strategy% (7236)------------------------------
% 1.29/0.54  % (7236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (7242)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.29/0.54  % (7236)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (7236)Memory used [KB]: 10746
% 1.29/0.54  % (7236)Time elapsed: 0.117 s
% 1.29/0.54  % (7236)------------------------------
% 1.29/0.54  % (7236)------------------------------
% 1.29/0.54  % (7231)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.29/0.54  % (7224)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (7224)Memory used [KB]: 10746
% 1.29/0.54  % (7224)Time elapsed: 0.119 s
% 1.29/0.54  % (7224)------------------------------
% 1.29/0.54  % (7224)------------------------------
% 1.29/0.54  % (7232)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.29/0.54  % (7226)Refutation not found, incomplete strategy% (7226)------------------------------
% 1.29/0.54  % (7226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (7226)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (7226)Memory used [KB]: 10618
% 1.29/0.54  % (7226)Time elapsed: 0.116 s
% 1.29/0.54  % (7226)------------------------------
% 1.29/0.54  % (7226)------------------------------
% 1.29/0.54  % (7220)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  % (7216)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  
% 1.29/0.54  % (7220)Memory used [KB]: 6140
% 1.29/0.54  % (7216)Memory used [KB]: 1663
% 1.29/0.54  % (7220)Time elapsed: 0.118 s
% 1.29/0.54  % (7216)Time elapsed: 0.117 s
% 1.29/0.54  % (7220)------------------------------
% 1.29/0.54  % (7220)------------------------------
% 1.29/0.54  % (7216)------------------------------
% 1.29/0.54  % (7216)------------------------------
% 1.29/0.54  % (7223)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.29/0.54  % (7218)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.29/0.55  % (7230)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.29/0.55  % (7218)Refutation not found, incomplete strategy% (7218)------------------------------
% 1.29/0.55  % (7218)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (7218)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (7218)Memory used [KB]: 10746
% 1.29/0.55  % (7218)Time elapsed: 0.128 s
% 1.29/0.55  % (7218)------------------------------
% 1.29/0.55  % (7218)------------------------------
% 1.29/0.55  % (7240)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.29/0.55  % (7243)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.29/0.55  % (7241)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.29/0.55  % (7238)Refutation not found, incomplete strategy% (7238)------------------------------
% 1.29/0.55  % (7238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (7235)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.46/0.56  % (7227)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.46/0.56  % (7233)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.46/0.56  % (7237)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.46/0.56  % (7233)Refutation not found, incomplete strategy% (7233)------------------------------
% 1.46/0.56  % (7233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (7233)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.56  
% 1.46/0.56  % (7233)Memory used [KB]: 10618
% 1.46/0.56  % (7233)Time elapsed: 0.138 s
% 1.46/0.56  % (7233)------------------------------
% 1.46/0.56  % (7233)------------------------------
% 1.46/0.56  % (7238)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.56  
% 1.46/0.56  % (7238)Memory used [KB]: 10746
% 1.46/0.56  % (7238)Time elapsed: 0.132 s
% 1.46/0.56  % (7238)------------------------------
% 1.46/0.56  % (7238)------------------------------
% 1.46/0.56  % (7229)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.46/0.57  % (7217)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.46/0.57  % (7225)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.46/0.57  % (7225)Refutation not found, incomplete strategy% (7225)------------------------------
% 1.46/0.57  % (7225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.57  % (7225)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.57  
% 1.46/0.57  % (7225)Memory used [KB]: 10618
% 1.46/0.57  % (7225)Time elapsed: 0.122 s
% 1.46/0.57  % (7225)------------------------------
% 1.46/0.57  % (7225)------------------------------
% 1.46/0.59  % (7245)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.46/0.62  % (7232)Refutation found. Thanks to Tanya!
% 1.46/0.62  % SZS status Theorem for theBenchmark
% 1.46/0.62  % SZS output start Proof for theBenchmark
% 1.46/0.62  fof(f1204,plain,(
% 1.46/0.62    $false),
% 1.46/0.62    inference(avatar_sat_refutation,[],[f83,f88,f93,f98,f103,f139,f226,f231,f248,f258,f287,f343,f356,f382,f412,f440,f452,f457,f463,f532,f819,f940,f951,f973,f980,f1041,f1190])).
% 1.46/0.62  fof(f1190,plain,(
% 1.46/0.62    ~spl7_9 | ~spl7_85),
% 1.46/0.62    inference(avatar_split_clause,[],[f1181,f1038,f136])).
% 1.46/0.62  fof(f136,plain,(
% 1.46/0.62    spl7_9 <=> v1_xboole_0(o_0_0_xboole_0)),
% 1.46/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.46/0.62  fof(f1038,plain,(
% 1.46/0.62    spl7_85 <=> r2_hidden(k4_tarski(sK5(k2_zfmisc_1(sK0,sK1)),sK5(sK2)),o_0_0_xboole_0)),
% 1.46/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_85])])).
% 1.46/0.62  fof(f1181,plain,(
% 1.46/0.62    ~v1_xboole_0(o_0_0_xboole_0) | ~spl7_85),
% 1.46/0.62    inference(resolution,[],[f1040,f43])).
% 1.46/0.62  fof(f43,plain,(
% 1.46/0.62    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.46/0.62    inference(cnf_transformation,[],[f23])).
% 1.89/0.65  fof(f23,plain,(
% 1.89/0.65    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.89/0.65    inference(ennf_transformation,[],[f20])).
% 1.89/0.65  fof(f20,plain,(
% 1.89/0.65    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.89/0.65    inference(unused_predicate_definition_removal,[],[f1])).
% 1.89/0.65  fof(f1,axiom,(
% 1.89/0.65    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.89/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.89/0.65  fof(f1040,plain,(
% 1.89/0.65    r2_hidden(k4_tarski(sK5(k2_zfmisc_1(sK0,sK1)),sK5(sK2)),o_0_0_xboole_0) | ~spl7_85),
% 1.89/0.65    inference(avatar_component_clause,[],[f1038])).
% 1.89/0.65  fof(f1041,plain,(
% 1.89/0.65    spl7_2 | spl7_37 | spl7_85 | ~spl7_8),
% 1.89/0.65    inference(avatar_split_clause,[],[f1007,f118,f1038,f366,f85])).
% 1.89/0.65  fof(f85,plain,(
% 1.89/0.65    spl7_2 <=> o_0_0_xboole_0 = sK2),
% 1.89/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.89/0.65  fof(f366,plain,(
% 1.89/0.65    spl7_37 <=> o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 1.89/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 1.89/0.65  fof(f118,plain,(
% 1.89/0.65    spl7_8 <=> o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 1.89/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.89/0.65  fof(f1007,plain,(
% 1.89/0.65    r2_hidden(k4_tarski(sK5(k2_zfmisc_1(sK0,sK1)),sK5(sK2)),o_0_0_xboole_0) | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1) | o_0_0_xboole_0 = sK2 | ~spl7_8),
% 1.89/0.65    inference(superposition,[],[f546,f120])).
% 1.89/0.65  fof(f120,plain,(
% 1.89/0.65    o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl7_8),
% 1.89/0.65    inference(avatar_component_clause,[],[f118])).
% 1.89/0.65  fof(f546,plain,(
% 1.89/0.65    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK5(X0),sK5(X1)),k2_zfmisc_1(X0,X1)) | o_0_0_xboole_0 = X0 | o_0_0_xboole_0 = X1) )),
% 1.89/0.65    inference(resolution,[],[f170,f71])).
% 1.89/0.65  fof(f71,plain,(
% 1.89/0.65    ( ! [X0] : (r2_hidden(sK5(X0),X0) | o_0_0_xboole_0 = X0) )),
% 1.89/0.65    inference(definition_unfolding,[],[f46,f42])).
% 1.89/0.65  fof(f42,plain,(
% 1.89/0.65    k1_xboole_0 = o_0_0_xboole_0),
% 1.89/0.65    inference(cnf_transformation,[],[f2])).
% 1.89/0.65  fof(f2,axiom,(
% 1.89/0.65    k1_xboole_0 = o_0_0_xboole_0),
% 1.89/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).
% 1.89/0.65  fof(f46,plain,(
% 1.89/0.65    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK5(X0),X0)) )),
% 1.89/0.65    inference(cnf_transformation,[],[f24])).
% 1.89/0.65  fof(f24,plain,(
% 1.89/0.65    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.89/0.65    inference(ennf_transformation,[],[f15])).
% 1.89/0.65  fof(f15,axiom,(
% 1.89/0.65    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.89/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).
% 1.89/0.65  fof(f170,plain,(
% 1.89/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(k4_tarski(sK5(X2),X0),k2_zfmisc_1(X2,X1)) | o_0_0_xboole_0 = X2) )),
% 1.89/0.65    inference(resolution,[],[f65,f71])).
% 1.89/0.65  fof(f65,plain,(
% 1.89/0.65    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X3) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.89/0.65    inference(cnf_transformation,[],[f4])).
% 1.89/0.65  fof(f4,axiom,(
% 1.89/0.65    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.89/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.89/0.65  fof(f980,plain,(
% 1.89/0.65    spl7_8 | ~spl7_7),
% 1.89/0.65    inference(avatar_split_clause,[],[f979,f112,f118])).
% 1.89/0.65  fof(f112,plain,(
% 1.89/0.65    spl7_7 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.89/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.89/0.65  fof(f979,plain,(
% 1.89/0.65    o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl7_7),
% 1.89/0.65    inference(resolution,[],[f114,f105])).
% 1.89/0.65  fof(f105,plain,(
% 1.89/0.65    ( ! [X1] : (~v1_xboole_0(X1) | o_0_0_xboole_0 = X1) )),
% 1.89/0.65    inference(resolution,[],[f71,f43])).
% 1.89/0.65  fof(f114,plain,(
% 1.89/0.65    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl7_7),
% 1.89/0.65    inference(avatar_component_clause,[],[f112])).
% 1.89/0.65  fof(f973,plain,(
% 1.89/0.65    spl7_6 | spl7_7 | ~spl7_5),
% 1.89/0.65    inference(avatar_split_clause,[],[f970,f100,f112,f108])).
% 1.89/0.65  fof(f108,plain,(
% 1.89/0.65    spl7_6 <=> r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.89/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.89/0.65  fof(f100,plain,(
% 1.89/0.65    spl7_5 <=> m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.89/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.89/0.65  fof(f970,plain,(
% 1.89/0.65    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl7_5),
% 1.89/0.65    inference(resolution,[],[f102,f50])).
% 1.89/0.65  fof(f50,plain,(
% 1.89/0.65    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.89/0.65    inference(cnf_transformation,[],[f29])).
% 1.89/0.65  fof(f29,plain,(
% 1.89/0.65    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.89/0.65    inference(flattening,[],[f28])).
% 1.89/0.65  fof(f28,plain,(
% 1.89/0.65    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.89/0.65    inference(ennf_transformation,[],[f6])).
% 1.89/0.65  fof(f6,axiom,(
% 1.89/0.65    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.89/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.89/0.65  fof(f102,plain,(
% 1.89/0.65    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl7_5),
% 1.89/0.65    inference(avatar_component_clause,[],[f100])).
% 1.89/0.65  fof(f951,plain,(
% 1.89/0.65    ~spl7_9 | ~spl7_76),
% 1.89/0.65    inference(avatar_split_clause,[],[f942,f937,f136])).
% 1.89/0.65  fof(f937,plain,(
% 1.89/0.65    spl7_76 <=> r2_hidden(k4_tarski(sK5(sK0),sK5(sK1)),o_0_0_xboole_0)),
% 1.89/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_76])])).
% 1.89/0.65  fof(f942,plain,(
% 1.89/0.65    ~v1_xboole_0(o_0_0_xboole_0) | ~spl7_76),
% 1.89/0.65    inference(resolution,[],[f939,f43])).
% 1.89/0.65  fof(f939,plain,(
% 1.89/0.65    r2_hidden(k4_tarski(sK5(sK0),sK5(sK1)),o_0_0_xboole_0) | ~spl7_76),
% 1.89/0.65    inference(avatar_component_clause,[],[f937])).
% 1.89/0.65  fof(f940,plain,(
% 1.89/0.65    spl7_3 | spl7_4 | spl7_76 | ~spl7_37),
% 1.89/0.65    inference(avatar_split_clause,[],[f934,f366,f937,f95,f90])).
% 1.89/0.65  fof(f90,plain,(
% 1.89/0.65    spl7_3 <=> o_0_0_xboole_0 = sK1),
% 1.89/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.89/0.65  fof(f95,plain,(
% 1.89/0.65    spl7_4 <=> o_0_0_xboole_0 = sK0),
% 1.89/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.89/0.65  fof(f934,plain,(
% 1.89/0.65    r2_hidden(k4_tarski(sK5(sK0),sK5(sK1)),o_0_0_xboole_0) | o_0_0_xboole_0 = sK0 | o_0_0_xboole_0 = sK1 | ~spl7_37),
% 1.89/0.65    inference(superposition,[],[f546,f368])).
% 1.89/0.65  fof(f368,plain,(
% 1.89/0.65    o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl7_37),
% 1.89/0.65    inference(avatar_component_clause,[],[f366])).
% 1.89/0.65  fof(f819,plain,(
% 1.89/0.65    ~spl7_18 | ~spl7_25 | ~spl7_39 | ~spl7_50 | ~spl7_54),
% 1.89/0.65    inference(avatar_split_clause,[],[f814,f461,f437,f375,f284,f241])).
% 1.89/0.65  fof(f241,plain,(
% 1.89/0.65    spl7_18 <=> sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))),
% 1.89/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 1.89/0.65  fof(f284,plain,(
% 1.89/0.65    spl7_25 <=> m1_subset_1(k2_mcart_1(sK4),sK2)),
% 1.89/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 1.89/0.65  fof(f375,plain,(
% 1.89/0.65    spl7_39 <=> k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))),
% 1.89/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 1.89/0.65  fof(f437,plain,(
% 1.89/0.65    spl7_50 <=> m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)),
% 1.89/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).
% 1.89/0.65  fof(f461,plain,(
% 1.89/0.65    spl7_54 <=> ! [X1,X0] : (~m1_subset_1(X0,sK1) | sK4 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),X0),X1) | ~m1_subset_1(X1,sK2))),
% 1.89/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).
% 1.89/0.65  fof(f814,plain,(
% 1.89/0.65    sK4 != k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | (~spl7_25 | ~spl7_39 | ~spl7_50 | ~spl7_54)),
% 1.89/0.65    inference(resolution,[],[f805,f286])).
% 1.89/0.65  fof(f286,plain,(
% 1.89/0.65    m1_subset_1(k2_mcart_1(sK4),sK2) | ~spl7_25),
% 1.89/0.65    inference(avatar_component_clause,[],[f284])).
% 1.89/0.65  fof(f805,plain,(
% 1.89/0.65    ( ! [X9] : (~m1_subset_1(X9,sK2) | sK4 != k4_tarski(k1_mcart_1(sK4),X9)) ) | (~spl7_39 | ~spl7_50 | ~spl7_54)),
% 1.89/0.65    inference(forward_demodulation,[],[f800,f377])).
% 1.89/0.65  fof(f377,plain,(
% 1.89/0.65    k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) | ~spl7_39),
% 1.89/0.65    inference(avatar_component_clause,[],[f375])).
% 1.89/0.65  fof(f800,plain,(
% 1.89/0.65    ( ! [X9] : (sK4 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))),X9) | ~m1_subset_1(X9,sK2)) ) | (~spl7_50 | ~spl7_54)),
% 1.89/0.65    inference(resolution,[],[f462,f439])).
% 1.89/0.65  fof(f439,plain,(
% 1.89/0.65    m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~spl7_50),
% 1.89/0.65    inference(avatar_component_clause,[],[f437])).
% 1.89/0.65  fof(f462,plain,(
% 1.89/0.65    ( ! [X0,X1] : (~m1_subset_1(X0,sK1) | sK4 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),X0),X1) | ~m1_subset_1(X1,sK2)) ) | ~spl7_54),
% 1.89/0.65    inference(avatar_component_clause,[],[f461])).
% 1.89/0.65  fof(f532,plain,(
% 1.89/0.65    spl7_19),
% 1.89/0.65    inference(avatar_contradiction_clause,[],[f531])).
% 1.89/0.65  fof(f531,plain,(
% 1.89/0.65    $false | spl7_19),
% 1.89/0.65    inference(resolution,[],[f247,f47])).
% 1.89/0.65  fof(f47,plain,(
% 1.89/0.65    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.89/0.65    inference(cnf_transformation,[],[f7])).
% 1.89/0.65  fof(f7,axiom,(
% 1.89/0.65    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.89/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.89/0.65  fof(f247,plain,(
% 1.89/0.65    ~v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | spl7_19),
% 1.89/0.65    inference(avatar_component_clause,[],[f245])).
% 1.89/0.65  fof(f245,plain,(
% 1.89/0.65    spl7_19 <=> v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.89/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 1.89/0.65  fof(f463,plain,(
% 1.89/0.65    spl7_53 | spl7_54 | ~spl7_52),
% 1.89/0.65    inference(avatar_split_clause,[],[f458,f449,f461,f454])).
% 1.89/0.65  fof(f454,plain,(
% 1.89/0.65    spl7_53 <=> sK3 = k1_mcart_1(k1_mcart_1(sK4))),
% 1.89/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).
% 1.89/0.65  fof(f449,plain,(
% 1.89/0.65    spl7_52 <=> m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)),
% 1.89/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).
% 1.89/0.65  fof(f458,plain,(
% 1.89/0.65    ( ! [X0,X1] : (~m1_subset_1(X0,sK1) | ~m1_subset_1(X1,sK2) | sK4 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),X0),X1) | sK3 = k1_mcart_1(k1_mcart_1(sK4))) ) | ~spl7_52),
% 1.89/0.65    inference(resolution,[],[f451,f70])).
% 1.89/0.65  fof(f70,plain,(
% 1.89/0.65    ( ! [X6,X7,X5] : (~m1_subset_1(X5,sK0) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | sK4 != k4_tarski(k4_tarski(X5,X6),X7) | sK3 = X5) )),
% 1.89/0.65    inference(definition_unfolding,[],[f36,f54])).
% 1.89/0.65  fof(f54,plain,(
% 1.89/0.65    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.89/0.65    inference(cnf_transformation,[],[f9])).
% 1.89/0.65  fof(f9,axiom,(
% 1.89/0.65    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.89/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.89/0.65  fof(f36,plain,(
% 1.89/0.65    ( ! [X6,X7,X5] : (~m1_subset_1(X5,sK0) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | k3_mcart_1(X5,X6,X7) != sK4 | sK3 = X5) )),
% 1.89/0.65    inference(cnf_transformation,[],[f22])).
% 1.89/0.65  fof(f22,plain,(
% 1.89/0.65    ? [X0,X1,X2,X3,X4] : (k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X5 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.89/0.65    inference(flattening,[],[f21])).
% 1.89/0.65  fof(f21,plain,(
% 1.89/0.65    ? [X0,X1,X2,X3,X4] : (((k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X5 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.89/0.65    inference(ennf_transformation,[],[f18])).
% 1.89/0.65  fof(f18,negated_conjecture,(
% 1.89/0.65    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X5)))) => (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.89/0.65    inference(negated_conjecture,[],[f17])).
% 1.89/0.65  fof(f17,conjecture,(
% 1.89/0.65    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X5)))) => (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.89/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_mcart_1)).
% 1.89/0.65  fof(f451,plain,(
% 1.89/0.65    m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | ~spl7_52),
% 1.89/0.65    inference(avatar_component_clause,[],[f449])).
% 1.89/0.65  fof(f457,plain,(
% 1.89/0.65    ~spl7_53 | spl7_1 | ~spl7_33),
% 1.89/0.65    inference(avatar_split_clause,[],[f447,f340,f80,f454])).
% 1.89/0.65  fof(f80,plain,(
% 1.89/0.65    spl7_1 <=> sK3 = k5_mcart_1(sK0,sK1,sK2,sK4)),
% 1.89/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.89/0.65  fof(f340,plain,(
% 1.89/0.65    spl7_33 <=> k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))),
% 1.89/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 1.89/0.65  fof(f447,plain,(
% 1.89/0.65    sK3 != k1_mcart_1(k1_mcart_1(sK4)) | (spl7_1 | ~spl7_33)),
% 1.89/0.65    inference(superposition,[],[f82,f342])).
% 1.89/0.65  fof(f342,plain,(
% 1.89/0.65    k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) | ~spl7_33),
% 1.89/0.65    inference(avatar_component_clause,[],[f340])).
% 1.89/0.65  fof(f82,plain,(
% 1.89/0.65    sK3 != k5_mcart_1(sK0,sK1,sK2,sK4) | spl7_1),
% 1.89/0.65    inference(avatar_component_clause,[],[f80])).
% 1.89/0.65  fof(f452,plain,(
% 1.89/0.65    spl7_52 | ~spl7_20 | ~spl7_33),
% 1.89/0.65    inference(avatar_split_clause,[],[f446,f340,f255,f449])).
% 1.89/0.65  fof(f255,plain,(
% 1.89/0.65    spl7_20 <=> m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0)),
% 1.89/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 1.89/0.65  fof(f446,plain,(
% 1.89/0.65    m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | (~spl7_20 | ~spl7_33)),
% 1.89/0.65    inference(backward_demodulation,[],[f257,f342])).
% 1.89/0.65  fof(f257,plain,(
% 1.89/0.65    m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) | ~spl7_20),
% 1.89/0.65    inference(avatar_component_clause,[],[f255])).
% 1.89/0.65  fof(f440,plain,(
% 1.89/0.65    spl7_50 | ~spl7_34),
% 1.89/0.65    inference(avatar_split_clause,[],[f417,f353,f437])).
% 1.89/0.65  fof(f353,plain,(
% 1.89/0.65    spl7_34 <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1)),
% 1.89/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 1.89/0.65  fof(f417,plain,(
% 1.89/0.65    m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~spl7_34),
% 1.89/0.65    inference(resolution,[],[f355,f49])).
% 1.89/0.65  fof(f49,plain,(
% 1.89/0.65    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 1.89/0.65    inference(cnf_transformation,[],[f27])).
% 1.89/0.65  fof(f27,plain,(
% 1.89/0.65    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.89/0.65    inference(ennf_transformation,[],[f5])).
% 1.89/0.65  fof(f5,axiom,(
% 1.89/0.65    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.89/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.89/0.65  fof(f355,plain,(
% 1.89/0.65    r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~spl7_34),
% 1.89/0.65    inference(avatar_component_clause,[],[f353])).
% 1.89/0.65  fof(f412,plain,(
% 1.89/0.65    spl7_40),
% 1.89/0.65    inference(avatar_contradiction_clause,[],[f411])).
% 1.89/0.65  fof(f411,plain,(
% 1.89/0.65    $false | spl7_40),
% 1.89/0.65    inference(resolution,[],[f381,f47])).
% 1.89/0.65  fof(f381,plain,(
% 1.89/0.65    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl7_40),
% 1.89/0.65    inference(avatar_component_clause,[],[f379])).
% 1.89/0.65  fof(f379,plain,(
% 1.89/0.65    spl7_40 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.89/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).
% 1.89/0.65  fof(f382,plain,(
% 1.89/0.65    spl7_39 | ~spl7_40 | ~spl7_15),
% 1.89/0.65    inference(avatar_split_clause,[],[f349,f228,f379,f375])).
% 1.89/0.65  fof(f228,plain,(
% 1.89/0.65    spl7_15 <=> r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))),
% 1.89/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 1.89/0.65  fof(f349,plain,(
% 1.89/0.65    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) | ~spl7_15),
% 1.89/0.65    inference(resolution,[],[f230,f48])).
% 1.89/0.65  fof(f48,plain,(
% 1.89/0.65    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_relat_1(X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) )),
% 1.89/0.65    inference(cnf_transformation,[],[f26])).
% 1.89/0.65  fof(f26,plain,(
% 1.89/0.65    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 1.89/0.65    inference(flattening,[],[f25])).
% 1.89/0.65  fof(f25,plain,(
% 1.89/0.65    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 1.89/0.65    inference(ennf_transformation,[],[f14])).
% 1.89/0.65  fof(f14,axiom,(
% 1.89/0.65    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 1.89/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).
% 1.89/0.65  fof(f230,plain,(
% 1.89/0.65    r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) | ~spl7_15),
% 1.89/0.65    inference(avatar_component_clause,[],[f228])).
% 1.89/0.65  fof(f356,plain,(
% 1.89/0.65    spl7_34 | ~spl7_15),
% 1.89/0.65    inference(avatar_split_clause,[],[f344,f228,f353])).
% 1.89/0.65  fof(f344,plain,(
% 1.89/0.65    r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~spl7_15),
% 1.89/0.65    inference(resolution,[],[f230,f57])).
% 1.89/0.65  fof(f57,plain,(
% 1.89/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 1.89/0.65    inference(cnf_transformation,[],[f32])).
% 1.89/0.65  fof(f32,plain,(
% 1.89/0.65    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.89/0.65    inference(ennf_transformation,[],[f13])).
% 1.89/0.65  fof(f13,axiom,(
% 1.89/0.65    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.89/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.89/0.65  fof(f343,plain,(
% 1.89/0.65    spl7_33 | spl7_4 | spl7_2 | spl7_3 | ~spl7_5),
% 1.89/0.65    inference(avatar_split_clause,[],[f335,f100,f90,f85,f95,f340])).
% 1.89/0.65  fof(f335,plain,(
% 1.89/0.65    o_0_0_xboole_0 = sK1 | o_0_0_xboole_0 = sK2 | o_0_0_xboole_0 = sK0 | k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) | ~spl7_5),
% 1.89/0.65    inference(resolution,[],[f76,f102])).
% 1.89/0.65  fof(f76,plain,(
% 1.89/0.65    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X2 | o_0_0_xboole_0 = X0 | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) )),
% 1.89/0.65    inference(definition_unfolding,[],[f58,f42,f42,f42,f55])).
% 1.89/0.65  fof(f55,plain,(
% 1.89/0.65    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.89/0.65    inference(cnf_transformation,[],[f10])).
% 1.89/0.65  fof(f10,axiom,(
% 1.89/0.65    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.89/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.89/0.65  fof(f58,plain,(
% 1.89/0.65    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) )),
% 1.89/0.65    inference(cnf_transformation,[],[f33])).
% 1.89/0.65  fof(f33,plain,(
% 1.89/0.65    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.89/0.65    inference(ennf_transformation,[],[f16])).
% 1.89/0.65  fof(f16,axiom,(
% 1.89/0.65    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.89/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 1.89/0.65  fof(f287,plain,(
% 1.89/0.65    spl7_25 | ~spl7_14),
% 1.89/0.65    inference(avatar_split_clause,[],[f264,f223,f284])).
% 1.89/0.65  fof(f223,plain,(
% 1.89/0.65    spl7_14 <=> r2_hidden(k2_mcart_1(sK4),sK2)),
% 1.89/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 1.89/0.65  fof(f264,plain,(
% 1.89/0.65    m1_subset_1(k2_mcart_1(sK4),sK2) | ~spl7_14),
% 1.89/0.65    inference(resolution,[],[f225,f49])).
% 1.89/0.65  fof(f225,plain,(
% 1.89/0.65    r2_hidden(k2_mcart_1(sK4),sK2) | ~spl7_14),
% 1.89/0.65    inference(avatar_component_clause,[],[f223])).
% 1.89/0.65  fof(f258,plain,(
% 1.89/0.65    spl7_20 | ~spl7_5),
% 1.89/0.65    inference(avatar_split_clause,[],[f251,f100,f255])).
% 1.89/0.65  fof(f251,plain,(
% 1.89/0.65    m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) | ~spl7_5),
% 1.89/0.65    inference(resolution,[],[f78,f102])).
% 1.89/0.65  fof(f78,plain,(
% 1.89/0.65    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)) )),
% 1.89/0.65    inference(definition_unfolding,[],[f62,f55])).
% 1.89/0.65  fof(f62,plain,(
% 1.89/0.65    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)) )),
% 1.89/0.65    inference(cnf_transformation,[],[f35])).
% 1.89/0.65  fof(f35,plain,(
% 1.89/0.65    ! [X0,X1,X2,X3] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 1.89/0.65    inference(ennf_transformation,[],[f11])).
% 1.89/0.65  fof(f11,axiom,(
% 1.89/0.65    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0))),
% 1.89/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_mcart_1)).
% 1.89/0.65  fof(f248,plain,(
% 1.89/0.65    spl7_18 | ~spl7_19 | ~spl7_6),
% 1.89/0.65    inference(avatar_split_clause,[],[f219,f108,f245,f241])).
% 1.89/0.65  fof(f219,plain,(
% 1.89/0.65    ~v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | ~spl7_6),
% 1.89/0.65    inference(resolution,[],[f110,f48])).
% 1.89/0.65  fof(f110,plain,(
% 1.89/0.65    r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl7_6),
% 1.89/0.65    inference(avatar_component_clause,[],[f108])).
% 1.89/0.65  fof(f231,plain,(
% 1.89/0.65    spl7_15 | ~spl7_6),
% 1.89/0.65    inference(avatar_split_clause,[],[f215,f108,f228])).
% 1.89/0.65  fof(f215,plain,(
% 1.89/0.65    r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) | ~spl7_6),
% 1.89/0.65    inference(resolution,[],[f110,f56])).
% 1.89/0.65  fof(f56,plain,(
% 1.89/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.89/0.65    inference(cnf_transformation,[],[f32])).
% 1.89/0.65  fof(f226,plain,(
% 1.89/0.65    spl7_14 | ~spl7_6),
% 1.89/0.65    inference(avatar_split_clause,[],[f214,f108,f223])).
% 1.89/0.65  fof(f214,plain,(
% 1.89/0.65    r2_hidden(k2_mcart_1(sK4),sK2) | ~spl7_6),
% 1.89/0.65    inference(resolution,[],[f110,f57])).
% 1.89/0.65  fof(f139,plain,(
% 1.89/0.65    spl7_9 | ~spl7_7 | ~spl7_8),
% 1.89/0.65    inference(avatar_split_clause,[],[f131,f118,f112,f136])).
% 1.89/0.65  fof(f131,plain,(
% 1.89/0.65    v1_xboole_0(o_0_0_xboole_0) | (~spl7_7 | ~spl7_8)),
% 1.89/0.65    inference(backward_demodulation,[],[f114,f120])).
% 1.89/0.65  fof(f103,plain,(
% 1.89/0.65    spl7_5),
% 1.89/0.65    inference(avatar_split_clause,[],[f69,f100])).
% 1.89/0.65  fof(f69,plain,(
% 1.89/0.65    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.89/0.65    inference(definition_unfolding,[],[f37,f55])).
% 1.89/0.65  fof(f37,plain,(
% 1.89/0.65    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.89/0.65    inference(cnf_transformation,[],[f22])).
% 1.89/0.65  fof(f98,plain,(
% 1.89/0.65    ~spl7_4),
% 1.89/0.65    inference(avatar_split_clause,[],[f68,f95])).
% 1.89/0.65  fof(f68,plain,(
% 1.89/0.65    o_0_0_xboole_0 != sK0),
% 1.89/0.65    inference(definition_unfolding,[],[f38,f42])).
% 1.89/0.65  fof(f38,plain,(
% 1.89/0.65    k1_xboole_0 != sK0),
% 1.89/0.65    inference(cnf_transformation,[],[f22])).
% 1.89/0.65  fof(f93,plain,(
% 1.89/0.65    ~spl7_3),
% 1.89/0.65    inference(avatar_split_clause,[],[f67,f90])).
% 1.89/0.65  fof(f67,plain,(
% 1.89/0.65    o_0_0_xboole_0 != sK1),
% 1.89/0.65    inference(definition_unfolding,[],[f39,f42])).
% 1.89/0.65  fof(f39,plain,(
% 1.89/0.65    k1_xboole_0 != sK1),
% 1.89/0.65    inference(cnf_transformation,[],[f22])).
% 1.89/0.65  fof(f88,plain,(
% 1.89/0.65    ~spl7_2),
% 1.89/0.65    inference(avatar_split_clause,[],[f66,f85])).
% 1.89/0.65  fof(f66,plain,(
% 1.89/0.65    o_0_0_xboole_0 != sK2),
% 1.89/0.65    inference(definition_unfolding,[],[f40,f42])).
% 1.89/0.65  fof(f40,plain,(
% 1.89/0.65    k1_xboole_0 != sK2),
% 1.89/0.65    inference(cnf_transformation,[],[f22])).
% 1.89/0.65  fof(f83,plain,(
% 1.89/0.65    ~spl7_1),
% 1.89/0.65    inference(avatar_split_clause,[],[f41,f80])).
% 1.89/0.65  fof(f41,plain,(
% 1.89/0.65    sK3 != k5_mcart_1(sK0,sK1,sK2,sK4)),
% 1.89/0.65    inference(cnf_transformation,[],[f22])).
% 1.89/0.65  % SZS output end Proof for theBenchmark
% 1.89/0.65  % (7232)------------------------------
% 1.89/0.65  % (7232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.65  % (7232)Termination reason: Refutation
% 1.89/0.65  
% 1.89/0.65  % (7232)Memory used [KB]: 11641
% 1.89/0.65  % (7232)Time elapsed: 0.213 s
% 1.89/0.65  % (7232)------------------------------
% 1.89/0.65  % (7232)------------------------------
% 1.89/0.65  % (7215)Success in time 0.282 s
%------------------------------------------------------------------------------
