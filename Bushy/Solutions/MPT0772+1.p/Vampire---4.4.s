%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord1__t21_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:11 EDT 2019

% Result     : Theorem 29.81s
% Output     : Refutation 29.81s
% Verified   : 
% Statistics : Number of formulae       :  346 (1342 expanded)
%              Number of leaves         :   79 ( 490 expanded)
%              Depth                    :   21
%              Number of atoms          : 1027 (4880 expanded)
%              Number of equality atoms :  104 ( 746 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2856,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f118,f125,f135,f157,f174,f184,f299,f306,f307,f324,f346,f353,f360,f367,f374,f375,f382,f383,f384,f412,f422,f426,f452,f459,f471,f504,f506,f513,f522,f532,f536,f639,f655,f682,f689,f719,f720,f878,f879,f880,f1027,f1231,f1238,f1403,f1940,f1941,f1942,f2027,f2028,f2134,f2135,f2181,f2231,f2390,f2464,f2532,f2536,f2543,f2589,f2596,f2616,f2840,f2841,f2842])).

fof(f2842,plain,
    ( ~ spl7_2
    | spl7_21
    | ~ spl7_32 ),
    inference(avatar_contradiction_clause,[],[f2830])).

fof(f2830,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_21
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f177,f323,f381,f777])).

fof(f777,plain,
    ( ! [X24,X23,X22] :
        ( ~ r1_tarski(X23,k2_wellord1(sK2,X22))
        | ~ r2_hidden(X24,X23)
        | r2_hidden(X24,sK2) )
    | ~ spl7_2 ),
    inference(superposition,[],[f202,f212])).

fof(f212,plain,
    ( ! [X0] : k2_wellord1(sK2,X0) = k3_xboole_0(sK2,k2_zfmisc_1(X0,X0))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f117,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t21_wellord1.p',d6_wellord1)).

fof(f117,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl7_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f202,plain,(
    ! [X14,X12,X13,X11] :
      ( ~ r1_tarski(X12,k3_xboole_0(X13,X14))
      | ~ r2_hidden(X11,X12)
      | r2_hidden(X11,X13) ) ),
    inference(resolution,[],[f83,f104])).

fof(f104,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK6(X0,X1,X2),X1)
              & r2_hidden(sK6(X0,X1,X2),X0) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f61,f62])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(sK6(X0,X1,X2),X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
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
    inference(rectify,[],[f60])).

fof(f60,plain,(
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
    inference(flattening,[],[f59])).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t21_wellord1.p',d4_xboole_0)).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f55,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t21_wellord1.p',d3_tarski)).

fof(f381,plain,
    ( r2_hidden(k4_tarski(sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),sK1),k2_wellord1(sK2,sK0))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f380])).

fof(f380,plain,
    ( spl7_32
  <=> r2_hidden(k4_tarski(sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),sK1),k2_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f323,plain,
    ( ~ r2_hidden(k4_tarski(sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),sK1),sK2)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f322])).

fof(f322,plain,
    ( spl7_21
  <=> ~ r2_hidden(k4_tarski(sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f177,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f176])).

fof(f176,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f85,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f2841,plain,
    ( ~ spl7_2
    | spl7_21
    | ~ spl7_32 ),
    inference(avatar_contradiction_clause,[],[f2775])).

fof(f2775,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_21
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f117,f323,f381,f218])).

fof(f218,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X3,k2_wellord1(X1,X2))
      | r2_hidden(X3,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f104,f68])).

fof(f2840,plain,
    ( ~ spl7_2
    | spl7_21
    | ~ spl7_32 ),
    inference(avatar_contradiction_clause,[],[f2771])).

fof(f2771,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_21
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f323,f381,f286])).

fof(f286,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X4,k2_wellord1(sK2,X3))
        | r2_hidden(X4,sK2) )
    | ~ spl7_2 ),
    inference(superposition,[],[f104,f212])).

fof(f2616,plain,
    ( ~ spl7_107
    | spl7_108
    | ~ spl7_2
    | spl7_9 ),
    inference(avatar_split_clause,[],[f2601,f155,f116,f2614,f2611])).

fof(f2611,plain,
    ( spl7_107
  <=> ~ r2_hidden(k1_wellord1(k2_wellord1(sK2,sK0),sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_107])])).

fof(f2614,plain,
    ( spl7_108
  <=> ! [X4] :
        ( ~ r1_tarski(k2_wellord1(sK2,X4),k1_zfmisc_1(k1_wellord1(sK2,sK1)))
        | ~ r2_hidden(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k2_zfmisc_1(X4,X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_108])])).

fof(f155,plain,
    ( spl7_9
  <=> ~ m1_subset_1(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_zfmisc_1(k1_wellord1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f2601,plain,
    ( ! [X4] :
        ( ~ r1_tarski(k2_wellord1(sK2,X4),k1_zfmisc_1(k1_wellord1(sK2,sK1)))
        | ~ r2_hidden(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k2_zfmisc_1(X4,X4))
        | ~ r2_hidden(k1_wellord1(k2_wellord1(sK2,sK0),sK1),sK2) )
    | ~ spl7_2
    | ~ spl7_9 ),
    inference(resolution,[],[f663,f285])).

fof(f285,plain,
    ( ! [X2,X1] :
        ( r2_hidden(X2,k2_wellord1(sK2,X1))
        | ~ r2_hidden(X2,k2_zfmisc_1(X1,X1))
        | ~ r2_hidden(X2,sK2) )
    | ~ spl7_2 ),
    inference(superposition,[],[f102,f212])).

fof(f102,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f663,plain,
    ( ! [X14] :
        ( ~ r2_hidden(k1_wellord1(k2_wellord1(sK2,sK0),sK1),X14)
        | ~ r1_tarski(X14,k1_zfmisc_1(k1_wellord1(sK2,sK1))) )
    | ~ spl7_9 ),
    inference(resolution,[],[f210,f156])).

fof(f156,plain,
    ( ~ m1_subset_1(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_zfmisc_1(k1_wellord1(sK2,sK1)))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f155])).

fof(f210,plain,(
    ! [X4,X2,X3] :
      ( m1_subset_1(X2,X3)
      | ~ r2_hidden(X2,X4)
      | ~ r1_tarski(X4,X3) ) ),
    inference(resolution,[],[f90,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t21_wellord1.p',t3_subset)).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t21_wellord1.p',t4_subset)).

fof(f2596,plain,
    ( ~ spl7_105
    | spl7_21
    | spl7_81 ),
    inference(avatar_split_clause,[],[f2571,f2022,f322,f2594])).

fof(f2594,plain,
    ( spl7_105
  <=> ~ m1_subset_1(k4_tarski(sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_105])])).

fof(f2022,plain,
    ( spl7_81
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_81])])).

fof(f2571,plain,
    ( ~ m1_subset_1(k4_tarski(sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),sK1),sK2)
    | ~ spl7_21
    | ~ spl7_81 ),
    inference(unit_resulting_resolution,[],[f2023,f323,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t21_wellord1.p',t2_subset)).

fof(f2023,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl7_81 ),
    inference(avatar_component_clause,[],[f2022])).

fof(f2589,plain,
    ( ~ spl7_103
    | spl7_21 ),
    inference(avatar_split_clause,[],[f2573,f322,f2587])).

fof(f2587,plain,
    ( spl7_103
  <=> ~ r2_hidden(k4_tarski(sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),sK1),sK4(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_103])])).

fof(f2573,plain,
    ( ~ r2_hidden(k4_tarski(sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),sK1),sK4(k1_zfmisc_1(sK2)))
    | ~ spl7_21 ),
    inference(unit_resulting_resolution,[],[f148,f323,f83])).

fof(f148,plain,(
    ! [X0] : r1_tarski(sK4(k1_zfmisc_1(X0)),X0) ),
    inference(unit_resulting_resolution,[],[f76,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f76,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t21_wellord1.p',existence_m1_subset_1)).

fof(f2543,plain,
    ( ~ spl7_101
    | spl7_17 ),
    inference(avatar_split_clause,[],[f2210,f304,f2541])).

fof(f2541,plain,
    ( spl7_101
  <=> ~ r2_hidden(k1_wellord1(k2_wellord1(sK2,sK0),sK1),sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_wellord1(sK2,sK1))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_101])])).

fof(f304,plain,
    ( spl7_17
  <=> ~ r2_hidden(k1_wellord1(k2_wellord1(sK2,sK0),sK1),sK4(k1_zfmisc_1(k1_zfmisc_1(k1_wellord1(sK2,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f2210,plain,
    ( ~ r2_hidden(k1_wellord1(k2_wellord1(sK2,sK0),sK1),sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_wellord1(sK2,sK1)))))))
    | ~ spl7_17 ),
    inference(unit_resulting_resolution,[],[f148,f305,f83])).

fof(f305,plain,
    ( ~ r2_hidden(k1_wellord1(k2_wellord1(sK2,sK0),sK1),sK4(k1_zfmisc_1(k1_zfmisc_1(k1_wellord1(sK2,sK1)))))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f304])).

fof(f2536,plain,
    ( spl7_98
    | spl7_96
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f2291,f116,f2530,f2534])).

fof(f2534,plain,
    ( spl7_98
  <=> ! [X10] :
        ( ~ r1_tarski(sK2,X10)
        | ~ v1_xboole_0(X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_98])])).

fof(f2530,plain,
    ( spl7_96
  <=> ! [X13,X14] : r1_tarski(k2_wellord1(sK2,X13),X14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_96])])).

fof(f2291,plain,
    ( ! [X10,X8,X9] :
        ( r1_tarski(k2_wellord1(sK2,X8),X9)
        | ~ r1_tarski(sK2,X10)
        | ~ v1_xboole_0(X10) )
    | ~ spl7_2 ),
    inference(resolution,[],[f998,f199])).

fof(f199,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,X4)
      | ~ r1_tarski(X4,X5)
      | ~ v1_xboole_0(X5) ) ),
    inference(resolution,[],[f83,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t21_wellord1.p',t7_boole)).

fof(f998,plain,
    ( ! [X21,X22] :
        ( r2_hidden(sK5(k2_wellord1(sK2,X21),X22),sK2)
        | r1_tarski(k2_wellord1(sK2,X21),X22) )
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f986,f212])).

fof(f986,plain,
    ( ! [X21,X22] :
        ( r2_hidden(sK5(k2_wellord1(sK2,X21),X22),sK2)
        | r1_tarski(k3_xboole_0(sK2,k2_zfmisc_1(X21,X21)),X22) )
    | ~ spl7_2 ),
    inference(superposition,[],[f192,f212])).

fof(f192,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(k3_xboole_0(X0,X1),X2),X0)
      | r1_tarski(k3_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f104,f84])).

fof(f2532,plain,
    ( ~ spl7_81
    | spl7_96
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f2293,f116,f2530,f2022])).

fof(f2293,plain,
    ( ! [X14,X13] :
        ( r1_tarski(k2_wellord1(sK2,X13),X14)
        | ~ v1_xboole_0(sK2) )
    | ~ spl7_2 ),
    inference(resolution,[],[f998,f89])).

fof(f2464,plain,
    ( ~ spl7_3
    | spl7_94
    | ~ spl7_2
    | ~ spl7_82 ),
    inference(avatar_split_clause,[],[f2460,f2025,f116,f2462,f113])).

fof(f113,plain,
    ( spl7_3
  <=> ~ v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f2462,plain,
    ( spl7_94
  <=> ! [X77,X79,X78] :
        ( k1_wellord1(sK2,X78) = X79
        | r2_hidden(k4_tarski(sK3(sK2,X78,X79),X78),k2_zfmisc_1(X77,X77))
        | r2_hidden(sK3(sK2,X78,X79),X79) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_94])])).

fof(f2025,plain,
    ( spl7_82
  <=> ! [X2] : k2_wellord1(sK2,X2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).

fof(f2460,plain,
    ( ! [X78,X79,X77] :
        ( k1_wellord1(sK2,X78) = X79
        | ~ v1_relat_1(sK2)
        | r2_hidden(sK3(sK2,X78,X79),X79)
        | r2_hidden(k4_tarski(sK3(sK2,X78,X79),X78),k2_zfmisc_1(X77,X77)) )
    | ~ spl7_2
    | ~ spl7_82 ),
    inference(forward_demodulation,[],[f2459,f2026])).

fof(f2026,plain,
    ( ! [X2] : k2_wellord1(sK2,X2) = sK2
    | ~ spl7_82 ),
    inference(avatar_component_clause,[],[f2025])).

fof(f2459,plain,
    ( ! [X78,X79,X77] :
        ( k1_wellord1(k2_wellord1(sK2,X77),X78) = X79
        | ~ v1_relat_1(sK2)
        | r2_hidden(sK3(sK2,X78,X79),X79)
        | r2_hidden(k4_tarski(sK3(sK2,X78,X79),X78),k2_zfmisc_1(X77,X77)) )
    | ~ spl7_2
    | ~ spl7_82 ),
    inference(forward_demodulation,[],[f2458,f2026])).

fof(f2458,plain,
    ( ! [X78,X76,X79,X77] :
        ( k1_wellord1(k2_wellord1(k2_wellord1(sK2,X76),X77),X78) = X79
        | ~ v1_relat_1(sK2)
        | r2_hidden(sK3(sK2,X78,X79),X79)
        | r2_hidden(k4_tarski(sK3(sK2,X78,X79),X78),k2_zfmisc_1(X77,X77)) )
    | ~ spl7_2
    | ~ spl7_82 ),
    inference(forward_demodulation,[],[f2457,f213])).

fof(f213,plain,
    ( ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k3_xboole_0(k2_wellord1(sK2,X0),k2_zfmisc_1(X1,X1))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f137,f68])).

fof(f137,plain,
    ( ! [X0] : v1_relat_1(k2_wellord1(sK2,X0))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f117,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t21_wellord1.p',dt_k2_wellord1)).

fof(f2457,plain,
    ( ! [X78,X76,X79,X77] :
        ( ~ v1_relat_1(sK2)
        | r2_hidden(sK3(sK2,X78,X79),X79)
        | r2_hidden(k4_tarski(sK3(sK2,X78,X79),X78),k2_zfmisc_1(X77,X77))
        | k1_wellord1(k3_xboole_0(k2_wellord1(sK2,X76),k2_zfmisc_1(X77,X77)),X78) = X79 )
    | ~ spl7_2
    | ~ spl7_82 ),
    inference(forward_demodulation,[],[f2456,f2026])).

fof(f2456,plain,
    ( ! [X78,X76,X79,X77] :
        ( ~ v1_relat_1(k2_wellord1(sK2,X77))
        | r2_hidden(sK3(sK2,X78,X79),X79)
        | r2_hidden(k4_tarski(sK3(sK2,X78,X79),X78),k2_zfmisc_1(X77,X77))
        | k1_wellord1(k3_xboole_0(k2_wellord1(sK2,X76),k2_zfmisc_1(X77,X77)),X78) = X79 )
    | ~ spl7_2
    | ~ spl7_82 ),
    inference(forward_demodulation,[],[f2455,f2026])).

fof(f2455,plain,
    ( ! [X78,X76,X79,X77] :
        ( ~ v1_relat_1(k2_wellord1(k2_wellord1(sK2,X76),X77))
        | r2_hidden(sK3(sK2,X78,X79),X79)
        | r2_hidden(k4_tarski(sK3(sK2,X78,X79),X78),k2_zfmisc_1(X77,X77))
        | k1_wellord1(k3_xboole_0(k2_wellord1(sK2,X76),k2_zfmisc_1(X77,X77)),X78) = X79 )
    | ~ spl7_2
    | ~ spl7_82 ),
    inference(forward_demodulation,[],[f2454,f213])).

fof(f2454,plain,
    ( ! [X78,X76,X79,X77] :
        ( r2_hidden(sK3(sK2,X78,X79),X79)
        | r2_hidden(k4_tarski(sK3(sK2,X78,X79),X78),k2_zfmisc_1(X77,X77))
        | ~ v1_relat_1(k3_xboole_0(k2_wellord1(sK2,X76),k2_zfmisc_1(X77,X77)))
        | k1_wellord1(k3_xboole_0(k2_wellord1(sK2,X76),k2_zfmisc_1(X77,X77)),X78) = X79 )
    | ~ spl7_2
    | ~ spl7_82 ),
    inference(forward_demodulation,[],[f2453,f2026])).

fof(f2453,plain,
    ( ! [X78,X76,X79,X77] :
        ( r2_hidden(sK3(k2_wellord1(sK2,X77),X78,X79),X79)
        | r2_hidden(k4_tarski(sK3(sK2,X78,X79),X78),k2_zfmisc_1(X77,X77))
        | ~ v1_relat_1(k3_xboole_0(k2_wellord1(sK2,X76),k2_zfmisc_1(X77,X77)))
        | k1_wellord1(k3_xboole_0(k2_wellord1(sK2,X76),k2_zfmisc_1(X77,X77)),X78) = X79 )
    | ~ spl7_2
    | ~ spl7_82 ),
    inference(forward_demodulation,[],[f2452,f2026])).

fof(f2452,plain,
    ( ! [X78,X76,X79,X77] :
        ( r2_hidden(sK3(k2_wellord1(k2_wellord1(sK2,X76),X77),X78,X79),X79)
        | r2_hidden(k4_tarski(sK3(sK2,X78,X79),X78),k2_zfmisc_1(X77,X77))
        | ~ v1_relat_1(k3_xboole_0(k2_wellord1(sK2,X76),k2_zfmisc_1(X77,X77)))
        | k1_wellord1(k3_xboole_0(k2_wellord1(sK2,X76),k2_zfmisc_1(X77,X77)),X78) = X79 )
    | ~ spl7_2
    | ~ spl7_82 ),
    inference(forward_demodulation,[],[f2451,f213])).

fof(f2451,plain,
    ( ! [X78,X76,X79,X77] :
        ( r2_hidden(k4_tarski(sK3(sK2,X78,X79),X78),k2_zfmisc_1(X77,X77))
        | r2_hidden(sK3(k3_xboole_0(k2_wellord1(sK2,X76),k2_zfmisc_1(X77,X77)),X78,X79),X79)
        | ~ v1_relat_1(k3_xboole_0(k2_wellord1(sK2,X76),k2_zfmisc_1(X77,X77)))
        | k1_wellord1(k3_xboole_0(k2_wellord1(sK2,X76),k2_zfmisc_1(X77,X77)),X78) = X79 )
    | ~ spl7_2
    | ~ spl7_82 ),
    inference(forward_demodulation,[],[f2450,f2026])).

fof(f2450,plain,
    ( ! [X78,X76,X79,X77] :
        ( r2_hidden(k4_tarski(sK3(k2_wellord1(sK2,X77),X78,X79),X78),k2_zfmisc_1(X77,X77))
        | r2_hidden(sK3(k3_xboole_0(k2_wellord1(sK2,X76),k2_zfmisc_1(X77,X77)),X78,X79),X79)
        | ~ v1_relat_1(k3_xboole_0(k2_wellord1(sK2,X76),k2_zfmisc_1(X77,X77)))
        | k1_wellord1(k3_xboole_0(k2_wellord1(sK2,X76),k2_zfmisc_1(X77,X77)),X78) = X79 )
    | ~ spl7_2
    | ~ spl7_82 ),
    inference(forward_demodulation,[],[f2333,f2026])).

fof(f2333,plain,
    ( ! [X78,X76,X79,X77] :
        ( r2_hidden(k4_tarski(sK3(k2_wellord1(k2_wellord1(sK2,X76),X77),X78,X79),X78),k2_zfmisc_1(X77,X77))
        | r2_hidden(sK3(k3_xboole_0(k2_wellord1(sK2,X76),k2_zfmisc_1(X77,X77)),X78,X79),X79)
        | ~ v1_relat_1(k3_xboole_0(k2_wellord1(sK2,X76),k2_zfmisc_1(X77,X77)))
        | k1_wellord1(k3_xboole_0(k2_wellord1(sK2,X76),k2_zfmisc_1(X77,X77)),X78) = X79 )
    | ~ spl7_2 ),
    inference(superposition,[],[f265,f213])).

fof(f265,plain,(
    ! [X12,X10,X13,X11] :
      ( r2_hidden(k4_tarski(sK3(k3_xboole_0(X10,X11),X12,X13),X12),X11)
      | r2_hidden(sK3(k3_xboole_0(X10,X11),X12,X13),X13)
      | ~ v1_relat_1(k3_xboole_0(X10,X11))
      | k1_wellord1(k3_xboole_0(X10,X11),X12) = X13 ) ),
    inference(resolution,[],[f73,f103])).

fof(f103,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0)
      | k1_wellord1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0)
                | sK3(X0,X1,X2) = X1
                | ~ r2_hidden(sK3(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0)
                  & sK3(X0,X1,X2) != X1 )
                | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f49,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0)
          | sK3(X0,X1,X2) = X1
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0)
            & sK3(X0,X1,X2) != X1 )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t21_wellord1.p',d1_wellord1)).

fof(f2390,plain,
    ( spl7_92
    | ~ spl7_3
    | ~ spl7_2
    | ~ spl7_82 ),
    inference(avatar_split_clause,[],[f2386,f2025,f116,f113,f2388])).

fof(f2388,plain,
    ( spl7_92
  <=> ! [X46,X45,X47] :
        ( ~ r2_hidden(X46,k1_wellord1(sK2,X47))
        | r2_hidden(k4_tarski(X46,X47),k2_zfmisc_1(X45,X45)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).

fof(f2386,plain,
    ( ! [X47,X45,X46] :
        ( ~ v1_relat_1(sK2)
        | ~ r2_hidden(X46,k1_wellord1(sK2,X47))
        | r2_hidden(k4_tarski(X46,X47),k2_zfmisc_1(X45,X45)) )
    | ~ spl7_2
    | ~ spl7_82 ),
    inference(forward_demodulation,[],[f2385,f2026])).

fof(f2385,plain,
    ( ! [X47,X45,X46] :
        ( ~ v1_relat_1(k2_wellord1(sK2,X45))
        | ~ r2_hidden(X46,k1_wellord1(sK2,X47))
        | r2_hidden(k4_tarski(X46,X47),k2_zfmisc_1(X45,X45)) )
    | ~ spl7_2
    | ~ spl7_82 ),
    inference(forward_demodulation,[],[f2384,f2026])).

fof(f2384,plain,
    ( ! [X47,X45,X46,X44] :
        ( ~ v1_relat_1(k2_wellord1(k2_wellord1(sK2,X44),X45))
        | ~ r2_hidden(X46,k1_wellord1(sK2,X47))
        | r2_hidden(k4_tarski(X46,X47),k2_zfmisc_1(X45,X45)) )
    | ~ spl7_2
    | ~ spl7_82 ),
    inference(forward_demodulation,[],[f2383,f213])).

fof(f2383,plain,
    ( ! [X47,X45,X46,X44] :
        ( ~ r2_hidden(X46,k1_wellord1(sK2,X47))
        | ~ v1_relat_1(k3_xboole_0(k2_wellord1(sK2,X44),k2_zfmisc_1(X45,X45)))
        | r2_hidden(k4_tarski(X46,X47),k2_zfmisc_1(X45,X45)) )
    | ~ spl7_2
    | ~ spl7_82 ),
    inference(forward_demodulation,[],[f2382,f2026])).

fof(f2382,plain,
    ( ! [X47,X45,X46,X44] :
        ( ~ r2_hidden(X46,k1_wellord1(k2_wellord1(sK2,X45),X47))
        | ~ v1_relat_1(k3_xboole_0(k2_wellord1(sK2,X44),k2_zfmisc_1(X45,X45)))
        | r2_hidden(k4_tarski(X46,X47),k2_zfmisc_1(X45,X45)) )
    | ~ spl7_2
    | ~ spl7_82 ),
    inference(forward_demodulation,[],[f2325,f2026])).

fof(f2325,plain,
    ( ! [X47,X45,X46,X44] :
        ( ~ r2_hidden(X46,k1_wellord1(k2_wellord1(k2_wellord1(sK2,X44),X45),X47))
        | ~ v1_relat_1(k3_xboole_0(k2_wellord1(sK2,X44),k2_zfmisc_1(X45,X45)))
        | r2_hidden(k4_tarski(X46,X47),k2_zfmisc_1(X45,X45)) )
    | ~ spl7_2 ),
    inference(superposition,[],[f241,f213])).

fof(f241,plain,(
    ! [X17,X15,X18,X16] :
      ( ~ r2_hidden(X15,k1_wellord1(k3_xboole_0(X16,X17),X18))
      | ~ v1_relat_1(k3_xboole_0(X16,X17))
      | r2_hidden(k4_tarski(X15,X18),X17) ) ),
    inference(resolution,[],[f99,f103])).

fof(f99,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f2231,plain,
    ( ~ spl7_91
    | spl7_17
    | ~ spl7_82 ),
    inference(avatar_split_clause,[],[f2224,f2025,f304,f2229])).

fof(f2229,plain,
    ( spl7_91
  <=> ~ r2_hidden(k1_wellord1(sK2,sK1),sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_wellord1(sK2,sK1))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_91])])).

fof(f2224,plain,
    ( ~ r2_hidden(k1_wellord1(sK2,sK1),sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_wellord1(sK2,sK1)))))))
    | ~ spl7_17
    | ~ spl7_82 ),
    inference(forward_demodulation,[],[f2210,f2026])).

fof(f2181,plain,
    ( ~ spl7_87
    | spl7_88
    | ~ spl7_10
    | spl7_13
    | ~ spl7_82 ),
    inference(avatar_split_clause,[],[f2171,f2025,f182,f172,f2179,f2176])).

fof(f2176,plain,
    ( spl7_87
  <=> ~ v1_relat_1(k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_87])])).

fof(f2179,plain,
    ( spl7_88
  <=> ! [X3] : ~ r1_tarski(k1_wellord1(sK2,sK1),k2_wellord1(k1_wellord1(sK2,sK1),X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_88])])).

fof(f172,plain,
    ( spl7_10
  <=> r2_hidden(sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),k1_wellord1(k2_wellord1(sK2,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f182,plain,
    ( spl7_13
  <=> ~ r2_hidden(sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f2171,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k1_wellord1(sK2,sK1),k2_wellord1(k1_wellord1(sK2,sK1),X3))
        | ~ v1_relat_1(k1_wellord1(sK2,sK1)) )
    | ~ spl7_10
    | ~ spl7_13
    | ~ spl7_82 ),
    inference(forward_demodulation,[],[f2162,f2026])).

fof(f2162,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k2_wellord1(k1_wellord1(sK2,sK1),X3))
        | ~ v1_relat_1(k1_wellord1(sK2,sK1)) )
    | ~ spl7_10
    | ~ spl7_13 ),
    inference(superposition,[],[f750,f68])).

fof(f750,plain,
    ( ! [X0] : ~ r1_tarski(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k3_xboole_0(k1_wellord1(sK2,sK1),X0))
    | ~ spl7_10
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f183,f173,f202])).

fof(f173,plain,
    ( r2_hidden(sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),k1_wellord1(k2_wellord1(sK2,sK0),sK1))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f172])).

fof(f183,plain,
    ( ~ r2_hidden(sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f182])).

fof(f2135,plain,
    ( spl7_84
    | spl7_81 ),
    inference(avatar_split_clause,[],[f2126,f2022,f2132])).

fof(f2132,plain,
    ( spl7_84
  <=> r2_hidden(sK4(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).

fof(f2126,plain,
    ( r2_hidden(sK4(sK2),sK2)
    | ~ spl7_81 ),
    inference(unit_resulting_resolution,[],[f2023,f162])).

fof(f162,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f82,f76])).

fof(f2134,plain,
    ( spl7_84
    | spl7_81 ),
    inference(avatar_split_clause,[],[f2127,f2022,f2132])).

fof(f2127,plain,
    ( r2_hidden(sK4(sK2),sK2)
    | ~ spl7_81 ),
    inference(unit_resulting_resolution,[],[f76,f2023,f82])).

fof(f2028,plain,
    ( ~ spl7_81
    | spl7_82
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f1998,f116,f2025,f2022])).

fof(f1998,plain,
    ( ! [X9] :
        ( k2_wellord1(sK2,X9) = sK2
        | ~ v1_xboole_0(sK2) )
    | ~ spl7_2 ),
    inference(superposition,[],[f128,f831])).

fof(f831,plain,
    ( ! [X0] : k2_wellord1(sK2,X0) = k3_xboole_0(k2_zfmisc_1(X0,X0),sK2)
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f117,f215])).

fof(f215,plain,(
    ! [X4,X3] :
      ( k2_wellord1(X3,X4) = k3_xboole_0(k2_zfmisc_1(X4,X4),X3)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f68,f78])).

fof(f78,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t21_wellord1.p',commutativity_k3_xboole_0)).

fof(f128,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,X0) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f67,f75])).

fof(f75,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t21_wellord1.p',t6_boole)).

fof(f67,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t21_wellord1.p',t2_boole)).

fof(f2027,plain,
    ( ~ spl7_81
    | spl7_82
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f1990,f116,f2025,f2022])).

fof(f1990,plain,
    ( ! [X2] :
        ( k2_wellord1(sK2,X2) = sK2
        | ~ v1_xboole_0(sK2) )
    | ~ spl7_2 ),
    inference(superposition,[],[f831,f128])).

fof(f1942,plain,
    ( ~ spl7_79
    | spl7_23 ),
    inference(avatar_split_clause,[],[f1927,f344,f1938])).

fof(f1938,plain,
    ( spl7_79
  <=> ~ r2_hidden(k1_wellord1(k2_wellord1(sK2,sK0),sK1),sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_79])])).

fof(f344,plain,
    ( spl7_23
  <=> ~ m1_subset_1(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f1927,plain,
    ( ~ r2_hidden(k1_wellord1(k2_wellord1(sK2,sK0),sK1),sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl7_23 ),
    inference(unit_resulting_resolution,[],[f148,f345,f210])).

fof(f345,plain,
    ( ~ m1_subset_1(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f344])).

fof(f1941,plain,
    ( ~ spl7_79
    | spl7_23 ),
    inference(avatar_split_clause,[],[f1928,f344,f1938])).

fof(f1928,plain,
    ( ~ r2_hidden(k1_wellord1(k2_wellord1(sK2,sK0),sK1),sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl7_23 ),
    inference(unit_resulting_resolution,[],[f345,f209])).

fof(f209,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK4(k1_zfmisc_1(X1)))
      | m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f90,f76])).

fof(f1940,plain,
    ( ~ spl7_79
    | spl7_23 ),
    inference(avatar_split_clause,[],[f1929,f344,f1938])).

fof(f1929,plain,
    ( ~ r2_hidden(k1_wellord1(k2_wellord1(sK2,sK0),sK1),sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl7_23 ),
    inference(unit_resulting_resolution,[],[f76,f345,f90])).

fof(f1403,plain,
    ( ~ spl7_77
    | ~ spl7_2
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f1384,f172,f116,f1401])).

fof(f1401,plain,
    ( spl7_77
  <=> ~ r1_tarski(k1_wellord1(k2_wellord1(sK2,sK0),sK1),sK4(k1_zfmisc_1(k1_wellord1(sK2,sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_77])])).

fof(f1384,plain,
    ( ~ r1_tarski(k1_wellord1(k2_wellord1(sK2,sK0),sK1),sK4(k1_zfmisc_1(k1_wellord1(sK2,sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1))))))
    | ~ spl7_2
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f173,f460,f83])).

fof(f460,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4(k1_zfmisc_1(k1_wellord1(sK2,X0))))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f160,f148,f83])).

fof(f160,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_wellord1(sK2,X0))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f117,f101])).

fof(f101,plain,(
    ! [X4,X0] :
      ( ~ r2_hidden(X4,k1_wellord1(X0,X4))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X4) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1238,plain,
    ( spl7_74
    | spl7_35 ),
    inference(avatar_split_clause,[],[f1216,f410,f1236])).

fof(f1236,plain,
    ( spl7_74
  <=> r2_hidden(sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),o_0_0_xboole_0),k1_wellord1(k2_wellord1(sK2,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).

fof(f410,plain,
    ( spl7_35
  <=> ~ r1_tarski(k1_wellord1(k2_wellord1(sK2,sK0),sK1),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f1216,plain,
    ( r2_hidden(sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),o_0_0_xboole_0),k1_wellord1(k2_wellord1(sK2,sK0),sK1))
    | ~ spl7_35 ),
    inference(unit_resulting_resolution,[],[f411,f84])).

fof(f411,plain,
    ( ~ r1_tarski(k1_wellord1(k2_wellord1(sK2,sK0),sK1),o_0_0_xboole_0)
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f410])).

fof(f1231,plain,
    ( ~ spl7_73
    | spl7_35 ),
    inference(avatar_split_clause,[],[f1220,f410,f1229])).

fof(f1229,plain,
    ( spl7_73
  <=> ~ r2_hidden(k1_wellord1(k2_wellord1(sK2,sK0),sK1),sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).

fof(f1220,plain,
    ( ~ r2_hidden(k1_wellord1(k2_wellord1(sK2,sK0),sK1),sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),o_0_0_xboole_0))
    | ~ spl7_35 ),
    inference(unit_resulting_resolution,[],[f411,f166])).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK5(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f84,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t21_wellord1.p',antisymmetry_r2_hidden)).

fof(f1027,plain,
    ( ~ spl7_71
    | ~ spl7_2
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f1008,f172,f116,f1025])).

fof(f1025,plain,
    ( spl7_71
  <=> ~ r2_hidden(k2_wellord1(sK2,sK0),k4_tarski(sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_71])])).

fof(f1008,plain,
    ( ~ r2_hidden(k2_wellord1(sK2,sK0),k4_tarski(sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),sK1))
    | ~ spl7_2
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f137,f173,f236])).

fof(f236,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k4_tarski(X0,X2))
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_wellord1(X1,X2)) ) ),
    inference(resolution,[],[f99,f80])).

fof(f880,plain,
    ( ~ spl7_2
    | spl7_67 ),
    inference(avatar_contradiction_clause,[],[f875])).

fof(f875,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_67 ),
    inference(unit_resulting_resolution,[],[f117,f688,f79])).

fof(f688,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | ~ spl7_67 ),
    inference(avatar_component_clause,[],[f687])).

fof(f687,plain,
    ( spl7_67
  <=> ~ v1_relat_1(k2_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).

fof(f879,plain,
    ( ~ spl7_2
    | spl7_67 ),
    inference(avatar_contradiction_clause,[],[f873])).

fof(f873,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_67 ),
    inference(unit_resulting_resolution,[],[f137,f688])).

fof(f878,plain,
    ( ~ spl7_2
    | spl7_67 ),
    inference(avatar_contradiction_clause,[],[f876])).

fof(f876,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_67 ),
    inference(resolution,[],[f688,f137])).

fof(f720,plain,
    ( spl7_68
    | spl7_65 ),
    inference(avatar_split_clause,[],[f711,f680,f717])).

fof(f717,plain,
    ( spl7_68
  <=> r2_hidden(sK4(k2_wellord1(sK2,sK0)),k2_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f680,plain,
    ( spl7_65
  <=> ~ v1_xboole_0(k2_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).

fof(f711,plain,
    ( r2_hidden(sK4(k2_wellord1(sK2,sK0)),k2_wellord1(sK2,sK0))
    | ~ spl7_65 ),
    inference(unit_resulting_resolution,[],[f681,f162])).

fof(f681,plain,
    ( ~ v1_xboole_0(k2_wellord1(sK2,sK0))
    | ~ spl7_65 ),
    inference(avatar_component_clause,[],[f680])).

fof(f719,plain,
    ( spl7_68
    | spl7_65 ),
    inference(avatar_split_clause,[],[f712,f680,f717])).

fof(f712,plain,
    ( r2_hidden(sK4(k2_wellord1(sK2,sK0)),k2_wellord1(sK2,sK0))
    | ~ spl7_65 ),
    inference(unit_resulting_resolution,[],[f76,f681,f82])).

fof(f689,plain,
    ( ~ spl7_65
    | ~ spl7_67
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f671,f172,f687,f680])).

fof(f671,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | ~ v1_xboole_0(k2_wellord1(sK2,sK0))
    | ~ spl7_10 ),
    inference(resolution,[],[f237,f173])).

fof(f237,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k1_wellord1(X4,X5))
      | ~ v1_relat_1(X4)
      | ~ v1_xboole_0(X4) ) ),
    inference(resolution,[],[f99,f89])).

fof(f682,plain,
    ( ~ spl7_65
    | ~ spl7_2
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f664,f172,f116,f680])).

fof(f664,plain,
    ( ~ v1_xboole_0(k2_wellord1(sK2,sK0))
    | ~ spl7_2
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f137,f173,f237])).

fof(f655,plain,
    ( ~ spl7_63
    | ~ spl7_4
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f640,f172,f123,f653])).

fof(f653,plain,
    ( spl7_63
  <=> ~ r2_hidden(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f123,plain,
    ( spl7_4
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f640,plain,
    ( ~ r2_hidden(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_4
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f124,f173,f208])).

fof(f208,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X7,k1_zfmisc_1(X5))
      | ~ r2_hidden(X6,X7)
      | ~ v1_xboole_0(X5) ) ),
    inference(resolution,[],[f97,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t21_wellord1.p',t1_subset)).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t21_wellord1.p',t5_subset)).

fof(f124,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f123])).

fof(f639,plain,
    ( ~ spl7_61
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f621,f172,f637])).

fof(f637,plain,
    ( spl7_61
  <=> ~ r2_hidden(k1_wellord1(k2_wellord1(sK2,sK0),sK1),sK4(k1_zfmisc_1(sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).

fof(f621,plain,
    ( ~ r2_hidden(k1_wellord1(k2_wellord1(sK2,sK0),sK1),sK4(k1_zfmisc_1(sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)))))
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f148,f173,f198])).

fof(f198,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X1,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f83,f80])).

fof(f536,plain,
    ( ~ spl7_55
    | spl7_58
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f492,f123,f534,f527])).

fof(f527,plain,
    ( spl7_55
  <=> ~ v1_relat_1(sK4(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f534,plain,
    ( spl7_58
  <=> ! [X5,X4] :
        ( k1_wellord1(sK4(k1_zfmisc_1(o_0_0_xboole_0)),X4) = X5
        | r2_hidden(sK3(sK4(k1_zfmisc_1(o_0_0_xboole_0)),X4,X5),X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f492,plain,
    ( ! [X4,X5] :
        ( k1_wellord1(sK4(k1_zfmisc_1(o_0_0_xboole_0)),X4) = X5
        | r2_hidden(sK3(sK4(k1_zfmisc_1(o_0_0_xboole_0)),X4,X5),X5)
        | ~ v1_relat_1(sK4(k1_zfmisc_1(o_0_0_xboole_0))) )
    | ~ spl7_4 ),
    inference(resolution,[],[f205,f73])).

fof(f205,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f124,f76,f97])).

fof(f532,plain,
    ( ~ spl7_55
    | spl7_56
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f491,f123,f530,f527])).

fof(f530,plain,
    ( spl7_56
  <=> ! [X3,X2] : ~ r2_hidden(X2,k1_wellord1(sK4(k1_zfmisc_1(o_0_0_xboole_0)),X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f491,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k1_wellord1(sK4(k1_zfmisc_1(o_0_0_xboole_0)),X3))
        | ~ v1_relat_1(sK4(k1_zfmisc_1(o_0_0_xboole_0))) )
    | ~ spl7_4 ),
    inference(resolution,[],[f205,f99])).

fof(f522,plain,
    ( ~ spl7_53
    | ~ spl7_4
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f475,f172,f123,f520])).

fof(f520,plain,
    ( spl7_53
  <=> ~ r1_tarski(k1_wellord1(k2_wellord1(sK2,sK0),sK1),sK4(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f475,plain,
    ( ~ r1_tarski(k1_wellord1(k2_wellord1(sK2,sK0),sK1),sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl7_4
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f173,f205,f83])).

fof(f513,plain,
    ( spl7_50
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f480,f123,f511])).

fof(f511,plain,
    ( spl7_50
  <=> v1_xboole_0(sK4(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f480,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f76,f205,f82])).

fof(f506,plain,
    ( spl7_48
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f505,f133,f123,f502])).

fof(f502,plain,
    ( spl7_48
  <=> o_0_0_xboole_0 = sK4(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f133,plain,
    ( spl7_6
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f505,plain,
    ( o_0_0_xboole_0 = sK4(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f482,f387])).

fof(f387,plain,
    ( ! [X0] : k3_xboole_0(X0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_6 ),
    inference(superposition,[],[f67,f134])).

fof(f134,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f133])).

fof(f482,plain,
    ( ! [X0] : k3_xboole_0(X0,o_0_0_xboole_0) = sK4(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f136,f205,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X2)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f136,plain,
    ( ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0)
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f124,f89])).

fof(f504,plain,
    ( spl7_48
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f497,f133,f123,f502])).

fof(f497,plain,
    ( o_0_0_xboole_0 = sK4(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f484,f143])).

fof(f143,plain,
    ( ! [X0] : k3_xboole_0(o_0_0_xboole_0,X0) = o_0_0_xboole_0
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f139,f134])).

fof(f139,plain,(
    ! [X0] : k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[],[f78,f67])).

fof(f484,plain,
    ( ! [X0] : k3_xboole_0(o_0_0_xboole_0,X0) = sK4(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f136,f205,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X2)
      | r2_hidden(sK6(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f471,plain,
    ( ~ spl7_47
    | spl7_13 ),
    inference(avatar_split_clause,[],[f462,f182,f469])).

fof(f469,plain,
    ( spl7_47
  <=> ~ r2_hidden(sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),sK4(k1_zfmisc_1(k1_wellord1(sK2,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f462,plain,
    ( ~ r2_hidden(sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),sK4(k1_zfmisc_1(k1_wellord1(sK2,sK1))))
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f183,f148,f83])).

fof(f459,plain,
    ( ~ spl7_45
    | ~ spl7_2
    | spl7_25 ),
    inference(avatar_split_clause,[],[f444,f351,f116,f457])).

fof(f457,plain,
    ( spl7_45
  <=> ~ m1_subset_1(sK1,k1_wellord1(k2_wellord1(sK2,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f351,plain,
    ( spl7_25
  <=> ~ v1_xboole_0(k1_wellord1(k2_wellord1(sK2,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f444,plain,
    ( ~ m1_subset_1(sK1,k1_wellord1(k2_wellord1(sK2,sK0),sK1))
    | ~ spl7_2
    | ~ spl7_25 ),
    inference(unit_resulting_resolution,[],[f161,f352,f82])).

fof(f352,plain,
    ( ~ v1_xboole_0(k1_wellord1(k2_wellord1(sK2,sK0),sK1))
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f351])).

fof(f161,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k1_wellord1(k2_wellord1(sK2,X1),X0))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f137,f101])).

fof(f452,plain,
    ( spl7_42
    | spl7_25 ),
    inference(avatar_split_clause,[],[f445,f351,f450])).

fof(f450,plain,
    ( spl7_42
  <=> r2_hidden(sK4(k1_wellord1(k2_wellord1(sK2,sK0),sK1)),k1_wellord1(k2_wellord1(sK2,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f445,plain,
    ( r2_hidden(sK4(k1_wellord1(k2_wellord1(sK2,sK0),sK1)),k1_wellord1(k2_wellord1(sK2,sK0),sK1))
    | ~ spl7_25 ),
    inference(unit_resulting_resolution,[],[f76,f352,f82])).

fof(f426,plain,
    ( ~ spl7_37
    | spl7_40
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f399,f123,f424,f417])).

fof(f417,plain,
    ( spl7_37
  <=> ~ v1_relat_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f424,plain,
    ( spl7_40
  <=> ! [X5,X4] :
        ( k1_wellord1(o_0_0_xboole_0,X4) = X5
        | r2_hidden(sK3(o_0_0_xboole_0,X4,X5),X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f399,plain,
    ( ! [X4,X5] :
        ( k1_wellord1(o_0_0_xboole_0,X4) = X5
        | r2_hidden(sK3(o_0_0_xboole_0,X4,X5),X5)
        | ~ v1_relat_1(o_0_0_xboole_0) )
    | ~ spl7_4 ),
    inference(resolution,[],[f136,f73])).

fof(f422,plain,
    ( ~ spl7_37
    | spl7_38
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f398,f123,f420,f417])).

fof(f420,plain,
    ( spl7_38
  <=> ! [X3,X2] : ~ r2_hidden(X2,k1_wellord1(o_0_0_xboole_0,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f398,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k1_wellord1(o_0_0_xboole_0,X3))
        | ~ v1_relat_1(o_0_0_xboole_0) )
    | ~ spl7_4 ),
    inference(resolution,[],[f136,f99])).

fof(f412,plain,
    ( ~ spl7_35
    | ~ spl7_4
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f388,f172,f123,f410])).

fof(f388,plain,
    ( ~ r1_tarski(k1_wellord1(k2_wellord1(sK2,sK0),sK1),o_0_0_xboole_0)
    | ~ spl7_4
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f173,f136,f83])).

fof(f384,plain,
    ( ~ spl7_25
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f337,f172,f351])).

fof(f337,plain,
    ( ~ v1_xboole_0(k1_wellord1(k2_wellord1(sK2,sK0),sK1))
    | ~ spl7_10 ),
    inference(resolution,[],[f173,f89])).

fof(f383,plain,
    ( ~ spl7_31
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f336,f172,f372])).

fof(f372,plain,
    ( spl7_31
  <=> ~ r2_hidden(k1_wellord1(k2_wellord1(sK2,sK0),sK1),sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f336,plain,
    ( ~ r2_hidden(k1_wellord1(k2_wellord1(sK2,sK0),sK1),sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)))
    | ~ spl7_10 ),
    inference(resolution,[],[f173,f80])).

fof(f382,plain,
    ( spl7_32
    | ~ spl7_2
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f325,f172,f116,f380])).

fof(f325,plain,
    ( r2_hidden(k4_tarski(sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),sK1),k2_wellord1(sK2,sK0))
    | ~ spl7_2
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f137,f173,f99])).

fof(f375,plain,
    ( ~ spl7_31
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f326,f172,f372])).

fof(f326,plain,
    ( ~ r2_hidden(k1_wellord1(k2_wellord1(sK2,sK0),sK1),sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)))
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f173,f80])).

fof(f374,plain,
    ( ~ spl7_31
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f327,f172,f372])).

fof(f327,plain,
    ( ~ r2_hidden(k1_wellord1(k2_wellord1(sK2,sK0),sK1),sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)))
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f173,f80])).

fof(f367,plain,
    ( spl7_28
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f328,f172,f365])).

fof(f365,plain,
    ( spl7_28
  <=> m1_subset_1(sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),k1_wellord1(k2_wellord1(sK2,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f328,plain,
    ( m1_subset_1(sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),k1_wellord1(k2_wellord1(sK2,sK0),sK1))
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f173,f81])).

fof(f360,plain,
    ( ~ spl7_27
    | ~ spl7_2
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f330,f172,f116,f358])).

fof(f358,plain,
    ( spl7_27
  <=> ~ r1_tarski(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f330,plain,
    ( ~ r1_tarski(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1))))
    | ~ spl7_2
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f160,f173,f83])).

fof(f353,plain,
    ( ~ spl7_25
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f332,f172,f351])).

fof(f332,plain,
    ( ~ v1_xboole_0(k1_wellord1(k2_wellord1(sK2,sK0),sK1))
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f173,f89])).

fof(f346,plain,
    ( ~ spl7_23
    | ~ spl7_4
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f333,f172,f123,f344])).

fof(f333,plain,
    ( ~ m1_subset_1(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_4
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f124,f173,f97])).

fof(f324,plain,
    ( ~ spl7_3
    | spl7_18
    | ~ spl7_21
    | spl7_13 ),
    inference(avatar_split_clause,[],[f310,f182,f322,f316,f113])).

fof(f316,plain,
    ( spl7_18
  <=> sK1 = sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f310,plain,
    ( ~ r2_hidden(k4_tarski(sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),sK1),sK2)
    | sK1 = sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl7_13 ),
    inference(resolution,[],[f183,f98])).

fof(f98,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f307,plain,
    ( ~ spl7_15
    | spl7_9 ),
    inference(avatar_split_clause,[],[f292,f155,f297])).

fof(f297,plain,
    ( spl7_15
  <=> ~ r2_hidden(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_zfmisc_1(k1_wellord1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f292,plain,
    ( ~ r2_hidden(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_zfmisc_1(k1_wellord1(sK2,sK1)))
    | ~ spl7_9 ),
    inference(resolution,[],[f156,f81])).

fof(f306,plain,
    ( ~ spl7_17
    | spl7_9 ),
    inference(avatar_split_clause,[],[f289,f155,f304])).

fof(f289,plain,
    ( ~ r2_hidden(k1_wellord1(k2_wellord1(sK2,sK0),sK1),sK4(k1_zfmisc_1(k1_zfmisc_1(k1_wellord1(sK2,sK1)))))
    | ~ spl7_9 ),
    inference(unit_resulting_resolution,[],[f76,f156,f90])).

fof(f299,plain,
    ( ~ spl7_15
    | spl7_9 ),
    inference(avatar_split_clause,[],[f290,f155,f297])).

fof(f290,plain,
    ( ~ r2_hidden(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_zfmisc_1(k1_wellord1(sK2,sK1)))
    | ~ spl7_9 ),
    inference(unit_resulting_resolution,[],[f156,f81])).

fof(f184,plain,
    ( ~ spl7_13
    | spl7_1 ),
    inference(avatar_split_clause,[],[f175,f109,f182])).

fof(f109,plain,
    ( spl7_1
  <=> ~ r1_tarski(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f175,plain,
    ( ~ r2_hidden(sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1))
    | ~ spl7_1 ),
    inference(unit_resulting_resolution,[],[f110,f85])).

fof(f110,plain,
    ( ~ r1_tarski(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f109])).

fof(f174,plain,
    ( spl7_10
    | spl7_1 ),
    inference(avatar_split_clause,[],[f165,f109,f172])).

fof(f165,plain,
    ( r2_hidden(sK5(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),k1_wellord1(k2_wellord1(sK2,sK0),sK1))
    | ~ spl7_1 ),
    inference(unit_resulting_resolution,[],[f110,f84])).

fof(f157,plain,
    ( ~ spl7_9
    | spl7_1 ),
    inference(avatar_split_clause,[],[f147,f109,f155])).

fof(f147,plain,
    ( ~ m1_subset_1(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_zfmisc_1(k1_wellord1(sK2,sK1)))
    | ~ spl7_1 ),
    inference(unit_resulting_resolution,[],[f110,f86])).

fof(f135,plain,
    ( spl7_6
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f126,f123,f133])).

fof(f126,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f124,f75])).

fof(f125,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f66,f123])).

fof(f66,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t21_wellord1.p',dt_o_0_0_xboole_0)).

fof(f118,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f64,f116])).

fof(f64,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ~ r1_tarski(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f45])).

fof(f45,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t21_wellord1.p',t21_wellord1)).

fof(f111,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f65,f109])).

fof(f65,plain,(
    ~ r1_tarski(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
