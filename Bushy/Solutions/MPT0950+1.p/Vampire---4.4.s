%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord2__t17_wellord2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:16 EDT 2019

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :  242 ( 447 expanded)
%              Number of leaves         :   58 ( 174 expanded)
%              Depth                    :   12
%              Number of atoms          :  705 (1254 expanded)
%              Number of equality atoms :   51 ( 130 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3177,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f151,f158,f170,f188,f198,f225,f232,f236,f247,f256,f265,f284,f322,f326,f419,f443,f462,f463,f526,f541,f546,f573,f578,f597,f741,f1048,f1061,f1073,f1354,f1553,f1640,f3174,f3176])).

fof(f3176,plain,
    ( k2_wellord2(k1_wellord2(sK0)) != sK6(sK0,k1_wellord2(sK1))
    | r1_tarski(k2_wellord2(k1_wellord2(sK0)),sK1)
    | ~ r1_tarski(sK6(sK0,k1_wellord2(sK1)),sK1) ),
    introduced(theory_axiom,[])).

fof(f3174,plain,
    ( spl7_394
    | ~ spl7_8
    | ~ spl7_72
    | ~ spl7_230 ),
    inference(avatar_split_clause,[],[f1652,f1638,f562,f186,f3172])).

fof(f3172,plain,
    ( spl7_394
  <=> k2_wellord2(k1_wellord2(sK0)) = sK6(sK0,k1_wellord2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_394])])).

fof(f186,plain,
    ( spl7_8
  <=> v2_wellord1(k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f562,plain,
    ( spl7_72
  <=> v3_ordinal1(sK6(sK0,k1_wellord2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).

fof(f1638,plain,
    ( spl7_230
  <=> r4_wellord1(k1_wellord2(sK6(sK0,k1_wellord2(sK1))),k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_230])])).

fof(f1652,plain,
    ( k2_wellord2(k1_wellord2(sK0)) = sK6(sK0,k1_wellord2(sK1))
    | ~ spl7_8
    | ~ spl7_72
    | ~ spl7_230 ),
    inference(subsumption_resolution,[],[f1651,f563])).

fof(f563,plain,
    ( v3_ordinal1(sK6(sK0,k1_wellord2(sK1)))
    | ~ spl7_72 ),
    inference(avatar_component_clause,[],[f562])).

fof(f1651,plain,
    ( k2_wellord2(k1_wellord2(sK0)) = sK6(sK0,k1_wellord2(sK1))
    | ~ v3_ordinal1(sK6(sK0,k1_wellord2(sK1)))
    | ~ spl7_8
    | ~ spl7_230 ),
    inference(resolution,[],[f1639,f277])).

fof(f277,plain,
    ( ! [X0] :
        ( ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(sK0))
        | k2_wellord2(k1_wellord2(sK0)) = X0
        | ~ v3_ordinal1(X0) )
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f276,f90])).

fof(f90,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',dt_k1_wellord2)).

fof(f276,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | k2_wellord2(k1_wellord2(sK0)) = X0
        | ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(sK0))
        | ~ v1_relat_1(k1_wellord2(X0)) )
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f274,f90])).

fof(f274,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | k2_wellord2(k1_wellord2(sK0)) = X0
        | ~ v1_relat_1(k1_wellord2(sK0))
        | ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(sK0))
        | ~ v1_relat_1(k1_wellord2(X0)) )
    | ~ spl7_8 ),
    inference(resolution,[],[f190,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',t50_wellord1)).

fof(f190,plain,
    ( ! [X0] :
        ( ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(X0))
        | ~ v3_ordinal1(X0)
        | k2_wellord2(k1_wellord2(sK0)) = X0 )
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f189,f90])).

fof(f189,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k1_wellord2(sK0))
        | ~ v3_ordinal1(X0)
        | ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(X0))
        | k2_wellord2(k1_wellord2(sK0)) = X0 )
    | ~ spl7_8 ),
    inference(resolution,[],[f187,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0)
      | ~ v3_ordinal1(X1)
      | ~ r4_wellord1(X0,k1_wellord2(X1))
      | k2_wellord2(X0) = X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_wellord2(X0) = X1
          <=> r4_wellord1(X0,k1_wellord2(X1)) )
          | ~ v3_ordinal1(X1) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_wellord2(X0) = X1
          <=> r4_wellord1(X0,k1_wellord2(X1)) )
          | ~ v3_ordinal1(X1) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( k2_wellord2(X0) = X1
            <=> r4_wellord1(X0,k1_wellord2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',d2_wellord2)).

fof(f187,plain,
    ( v2_wellord1(k1_wellord2(sK0))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f186])).

fof(f1639,plain,
    ( r4_wellord1(k1_wellord2(sK6(sK0,k1_wellord2(sK1))),k1_wellord2(sK0))
    | ~ spl7_230 ),
    inference(avatar_component_clause,[],[f1638])).

fof(f1640,plain,
    ( spl7_230
    | ~ spl7_196
    | ~ spl7_216 ),
    inference(avatar_split_clause,[],[f1567,f1532,f1352,f1638])).

fof(f1352,plain,
    ( spl7_196
  <=> r4_wellord1(k2_wellord1(k1_wellord2(sK1),sK6(sK0,k1_wellord2(sK1))),k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_196])])).

fof(f1532,plain,
    ( spl7_216
  <=> k1_wellord2(sK6(sK0,k1_wellord2(sK1))) = k2_wellord1(k1_wellord2(sK1),sK6(sK0,k1_wellord2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_216])])).

fof(f1567,plain,
    ( r4_wellord1(k1_wellord2(sK6(sK0,k1_wellord2(sK1))),k1_wellord2(sK0))
    | ~ spl7_196
    | ~ spl7_216 ),
    inference(superposition,[],[f1353,f1533])).

fof(f1533,plain,
    ( k1_wellord2(sK6(sK0,k1_wellord2(sK1))) = k2_wellord1(k1_wellord2(sK1),sK6(sK0,k1_wellord2(sK1)))
    | ~ spl7_216 ),
    inference(avatar_component_clause,[],[f1532])).

fof(f1353,plain,
    ( r4_wellord1(k2_wellord1(k1_wellord2(sK1),sK6(sK0,k1_wellord2(sK1))),k1_wellord2(sK0))
    | ~ spl7_196 ),
    inference(avatar_component_clause,[],[f1352])).

fof(f1553,plain,
    ( spl7_216
    | ~ spl7_100 ),
    inference(avatar_split_clause,[],[f753,f739,f1532])).

fof(f739,plain,
    ( spl7_100
  <=> k1_wellord2(sK6(sK0,k1_wellord2(sK1))) = k2_wellord1(k1_wellord2(k3_relat_1(k1_wellord2(sK1))),sK6(sK0,k1_wellord2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_100])])).

fof(f753,plain,
    ( k1_wellord2(sK6(sK0,k1_wellord2(sK1))) = k2_wellord1(k1_wellord2(sK1),sK6(sK0,k1_wellord2(sK1)))
    | ~ spl7_100 ),
    inference(subsumption_resolution,[],[f749,f90])).

fof(f749,plain,
    ( k1_wellord2(sK6(sK0,k1_wellord2(sK1))) = k2_wellord1(k1_wellord2(sK1),sK6(sK0,k1_wellord2(sK1)))
    | ~ v1_relat_1(k1_wellord2(sK1))
    | ~ spl7_100 ),
    inference(superposition,[],[f740,f137])).

fof(f137,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',d1_wellord2)).

fof(f740,plain,
    ( k1_wellord2(sK6(sK0,k1_wellord2(sK1))) = k2_wellord1(k1_wellord2(k3_relat_1(k1_wellord2(sK1))),sK6(sK0,k1_wellord2(sK1)))
    | ~ spl7_100 ),
    inference(avatar_component_clause,[],[f739])).

fof(f1354,plain,
    ( spl7_196
    | ~ spl7_54
    | ~ spl7_94 ),
    inference(avatar_split_clause,[],[f1080,f702,f460,f1352])).

fof(f460,plain,
    ( spl7_54
  <=> r4_wellord1(k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),sK6(sK0,k1_wellord2(sK1)))),k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f702,plain,
    ( spl7_94
  <=> k1_wellord1(k1_wellord2(sK1),sK6(sK0,k1_wellord2(sK1))) = sK6(sK0,k1_wellord2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_94])])).

fof(f1080,plain,
    ( r4_wellord1(k2_wellord1(k1_wellord2(sK1),sK6(sK0,k1_wellord2(sK1))),k1_wellord2(sK0))
    | ~ spl7_54
    | ~ spl7_94 ),
    inference(superposition,[],[f461,f703])).

fof(f703,plain,
    ( k1_wellord1(k1_wellord2(sK1),sK6(sK0,k1_wellord2(sK1))) = sK6(sK0,k1_wellord2(sK1))
    | ~ spl7_94 ),
    inference(avatar_component_clause,[],[f702])).

fof(f461,plain,
    ( r4_wellord1(k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),sK6(sK0,k1_wellord2(sK1)))),k1_wellord2(sK0))
    | ~ spl7_54 ),
    inference(avatar_component_clause,[],[f460])).

fof(f1073,plain,
    ( ~ spl7_70
    | spl7_95 ),
    inference(avatar_contradiction_clause,[],[f1072])).

fof(f1072,plain,
    ( $false
    | ~ spl7_70
    | ~ spl7_95 ),
    inference(subsumption_resolution,[],[f1071,f90])).

fof(f1071,plain,
    ( ~ v1_relat_1(k1_wellord2(sK1))
    | ~ spl7_70
    | ~ spl7_95 ),
    inference(subsumption_resolution,[],[f1070,f706])).

fof(f706,plain,
    ( k1_wellord1(k1_wellord2(sK1),sK6(sK0,k1_wellord2(sK1))) != sK6(sK0,k1_wellord2(sK1))
    | ~ spl7_95 ),
    inference(avatar_component_clause,[],[f705])).

fof(f705,plain,
    ( spl7_95
  <=> k1_wellord1(k1_wellord2(sK1),sK6(sK0,k1_wellord2(sK1))) != sK6(sK0,k1_wellord2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_95])])).

fof(f1070,plain,
    ( k1_wellord1(k1_wellord2(sK1),sK6(sK0,k1_wellord2(sK1))) = sK6(sK0,k1_wellord2(sK1))
    | ~ v1_relat_1(k1_wellord2(sK1))
    | ~ spl7_70 ),
    inference(superposition,[],[f560,f137])).

fof(f560,plain,
    ( k1_wellord1(k1_wellord2(k3_relat_1(k1_wellord2(sK1))),sK6(sK0,k1_wellord2(sK1))) = sK6(sK0,k1_wellord2(sK1))
    | ~ spl7_70 ),
    inference(avatar_component_clause,[],[f559])).

fof(f559,plain,
    ( spl7_70
  <=> k1_wellord1(k1_wellord2(k3_relat_1(k1_wellord2(sK1))),sK6(sK0,k1_wellord2(sK1))) = sK6(sK0,k1_wellord2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f1061,plain,
    ( ~ spl7_0
    | spl7_73
    | ~ spl7_150 ),
    inference(avatar_contradiction_clause,[],[f1060])).

fof(f1060,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_73
    | ~ spl7_150 ),
    inference(subsumption_resolution,[],[f1059,f150])).

fof(f150,plain,
    ( v3_ordinal1(sK1)
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl7_0
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f1059,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ spl7_73
    | ~ spl7_150 ),
    inference(resolution,[],[f1047,f581])).

fof(f581,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6(sK0,k1_wellord2(sK1)),X0)
        | ~ v3_ordinal1(X0) )
    | ~ spl7_73 ),
    inference(resolution,[],[f566,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_ordinal1(X1)
          | ~ m1_subset_1(X1,X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',cc5_ordinal1)).

fof(f566,plain,
    ( ~ v3_ordinal1(sK6(sK0,k1_wellord2(sK1)))
    | ~ spl7_73 ),
    inference(avatar_component_clause,[],[f565])).

fof(f565,plain,
    ( spl7_73
  <=> ~ v3_ordinal1(sK6(sK0,k1_wellord2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).

fof(f1047,plain,
    ( m1_subset_1(sK6(sK0,k1_wellord2(sK1)),sK1)
    | ~ spl7_150 ),
    inference(avatar_component_clause,[],[f1046])).

fof(f1046,plain,
    ( spl7_150
  <=> m1_subset_1(sK6(sK0,k1_wellord2(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_150])])).

fof(f1048,plain,
    ( spl7_150
    | ~ spl7_18
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f650,f342,f245,f1046])).

fof(f245,plain,
    ( spl7_18
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f342,plain,
    ( spl7_36
  <=> r2_hidden(sK6(sK0,k1_wellord2(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f650,plain,
    ( m1_subset_1(sK6(sK0,k1_wellord2(sK1)),sK1)
    | ~ spl7_18
    | ~ spl7_36 ),
    inference(resolution,[],[f477,f246])).

fof(f246,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f245])).

fof(f477,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | m1_subset_1(sK6(sK0,k1_wellord2(sK1)),X0) )
    | ~ spl7_36 ),
    inference(resolution,[],[f343,f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f83])).

fof(f83,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',t4_subset)).

fof(f343,plain,
    ( r2_hidden(sK6(sK0,k1_wellord2(sK1)),sK1)
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f342])).

fof(f741,plain,
    ( spl7_100
    | ~ spl7_66 ),
    inference(avatar_split_clause,[],[f551,f524,f739])).

fof(f524,plain,
    ( spl7_66
  <=> r1_tarski(sK6(sK0,k1_wellord2(sK1)),k3_relat_1(k1_wellord2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f551,plain,
    ( k1_wellord2(sK6(sK0,k1_wellord2(sK1))) = k2_wellord1(k1_wellord2(k3_relat_1(k1_wellord2(sK1))),sK6(sK0,k1_wellord2(sK1)))
    | ~ spl7_66 ),
    inference(resolution,[],[f525,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',t8_wellord2)).

fof(f525,plain,
    ( r1_tarski(sK6(sK0,k1_wellord2(sK1)),k3_relat_1(k1_wellord2(sK1)))
    | ~ spl7_66 ),
    inference(avatar_component_clause,[],[f524])).

fof(f597,plain,
    ( spl7_78
    | ~ spl7_66 ),
    inference(avatar_split_clause,[],[f554,f524,f595])).

fof(f595,plain,
    ( spl7_78
  <=> r1_tarski(sK6(sK0,k1_wellord2(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).

fof(f554,plain,
    ( r1_tarski(sK6(sK0,k1_wellord2(sK1)),sK1)
    | ~ spl7_66 ),
    inference(subsumption_resolution,[],[f553,f90])).

fof(f553,plain,
    ( r1_tarski(sK6(sK0,k1_wellord2(sK1)),sK1)
    | ~ v1_relat_1(k1_wellord2(sK1))
    | ~ spl7_66 ),
    inference(superposition,[],[f525,f137])).

fof(f578,plain,
    ( ~ spl7_0
    | spl7_75 ),
    inference(avatar_contradiction_clause,[],[f577])).

fof(f577,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_75 ),
    inference(subsumption_resolution,[],[f576,f90])).

fof(f576,plain,
    ( ~ v1_relat_1(k1_wellord2(sK1))
    | ~ spl7_0
    | ~ spl7_75 ),
    inference(subsumption_resolution,[],[f575,f150])).

fof(f575,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v1_relat_1(k1_wellord2(sK1))
    | ~ spl7_75 ),
    inference(superposition,[],[f572,f137])).

fof(f572,plain,
    ( ~ v3_ordinal1(k3_relat_1(k1_wellord2(sK1)))
    | ~ spl7_75 ),
    inference(avatar_component_clause,[],[f571])).

fof(f571,plain,
    ( spl7_75
  <=> ~ v3_ordinal1(k3_relat_1(k1_wellord2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).

fof(f573,plain,
    ( spl7_70
    | ~ spl7_73
    | ~ spl7_75
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f432,f308,f571,f565,f559])).

fof(f308,plain,
    ( spl7_28
  <=> r2_hidden(sK6(sK0,k1_wellord2(sK1)),k3_relat_1(k1_wellord2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f432,plain,
    ( ~ v3_ordinal1(k3_relat_1(k1_wellord2(sK1)))
    | ~ v3_ordinal1(sK6(sK0,k1_wellord2(sK1)))
    | k1_wellord1(k1_wellord2(k3_relat_1(k1_wellord2(sK1))),sK6(sK0,k1_wellord2(sK1))) = sK6(sK0,k1_wellord2(sK1))
    | ~ spl7_28 ),
    inference(resolution,[],[f309,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | k1_wellord1(k1_wellord2(X1),X0) = X0 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',t10_wellord2)).

fof(f309,plain,
    ( r2_hidden(sK6(sK0,k1_wellord2(sK1)),k3_relat_1(k1_wellord2(sK1)))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f308])).

fof(f546,plain,
    ( ~ spl7_0
    | spl7_69 ),
    inference(avatar_contradiction_clause,[],[f545])).

fof(f545,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_69 ),
    inference(subsumption_resolution,[],[f544,f150])).

fof(f544,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ spl7_69 ),
    inference(resolution,[],[f540,f99])).

fof(f99,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f46,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',cc1_ordinal1)).

fof(f540,plain,
    ( ~ v1_ordinal1(sK1)
    | ~ spl7_69 ),
    inference(avatar_component_clause,[],[f539])).

fof(f539,plain,
    ( spl7_69
  <=> ~ v1_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_69])])).

fof(f541,plain,
    ( ~ spl7_69
    | spl7_65 ),
    inference(avatar_split_clause,[],[f531,f518,f539])).

fof(f518,plain,
    ( spl7_65
  <=> ~ v1_ordinal1(k3_relat_1(k1_wellord2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).

fof(f531,plain,
    ( ~ v1_ordinal1(sK1)
    | ~ spl7_65 ),
    inference(subsumption_resolution,[],[f530,f90])).

fof(f530,plain,
    ( ~ v1_ordinal1(sK1)
    | ~ v1_relat_1(k1_wellord2(sK1))
    | ~ spl7_65 ),
    inference(superposition,[],[f519,f137])).

fof(f519,plain,
    ( ~ v1_ordinal1(k3_relat_1(k1_wellord2(sK1)))
    | ~ spl7_65 ),
    inference(avatar_component_clause,[],[f518])).

fof(f526,plain,
    ( ~ spl7_65
    | spl7_66
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f433,f308,f524,f518])).

fof(f433,plain,
    ( r1_tarski(sK6(sK0,k1_wellord2(sK1)),k3_relat_1(k1_wellord2(sK1)))
    | ~ v1_ordinal1(k3_relat_1(k1_wellord2(sK1)))
    | ~ spl7_28 ),
    inference(resolution,[],[f309,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | r1_tarski(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',d2_ordinal1)).

fof(f463,plain,
    ( k2_wellord2(k1_wellord2(sK0)) != sK1
    | r1_ordinal1(k2_wellord2(k1_wellord2(sK0)),sK1)
    | ~ r1_ordinal1(sK1,k2_wellord2(k1_wellord2(sK0))) ),
    introduced(theory_axiom,[])).

fof(f462,plain,
    ( spl7_54
    | ~ spl7_10
    | ~ spl7_24
    | ~ spl7_30
    | spl7_33 ),
    inference(avatar_split_clause,[],[f452,f317,f311,f282,f196,f460])).

fof(f196,plain,
    ( spl7_10
  <=> k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f282,plain,
    ( spl7_24
  <=> v2_wellord1(k1_wellord2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f311,plain,
    ( spl7_30
  <=> r1_tarski(sK0,k3_relat_1(k1_wellord2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f317,plain,
    ( spl7_33
  <=> ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f452,plain,
    ( r4_wellord1(k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),sK6(sK0,k1_wellord2(sK1)))),k1_wellord2(sK0))
    | ~ spl7_10
    | ~ spl7_24
    | ~ spl7_30
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f421,f318])).

fof(f318,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f317])).

fof(f421,plain,
    ( r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | r4_wellord1(k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),sK6(sK0,k1_wellord2(sK1)))),k1_wellord2(sK0))
    | ~ spl7_10
    | ~ spl7_24
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f420,f283])).

fof(f283,plain,
    ( v2_wellord1(k1_wellord2(sK1))
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f282])).

fof(f420,plain,
    ( r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | r4_wellord1(k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),sK6(sK0,k1_wellord2(sK1)))),k1_wellord2(sK0))
    | ~ v2_wellord1(k1_wellord2(sK1))
    | ~ spl7_10
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f204,f312])).

fof(f312,plain,
    ( r1_tarski(sK0,k3_relat_1(k1_wellord2(sK1)))
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f311])).

fof(f204,plain,
    ( r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | r4_wellord1(k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),sK6(sK0,k1_wellord2(sK1)))),k1_wellord2(sK0))
    | ~ r1_tarski(sK0,k3_relat_1(k1_wellord2(sK1)))
    | ~ v2_wellord1(k1_wellord2(sK1))
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f203,f197])).

fof(f197,plain,
    ( k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f196])).

fof(f203,plain,
    ( r4_wellord1(k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),sK6(sK0,k1_wellord2(sK1)))),k1_wellord2(sK0))
    | ~ r1_tarski(sK0,k3_relat_1(k1_wellord2(sK1)))
    | ~ v2_wellord1(k1_wellord2(sK1))
    | r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f200,f90])).

fof(f200,plain,
    ( r4_wellord1(k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),sK6(sK0,k1_wellord2(sK1)))),k1_wellord2(sK0))
    | ~ r1_tarski(sK0,k3_relat_1(k1_wellord2(sK1)))
    | ~ v2_wellord1(k1_wellord2(sK1))
    | r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ v1_relat_1(k1_wellord2(sK1))
    | ~ spl7_10 ),
    inference(superposition,[],[f121,f197])).

fof(f121,plain,(
    ! [X0,X1] :
      ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,sK6(X0,X1))),k2_wellord1(X1,X0))
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | r4_wellord1(X1,k2_wellord1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,X2)),k2_wellord1(X1,X0))
          & r2_hidden(X2,k3_relat_1(X1)) )
      | r4_wellord1(X1,k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,X2)),k2_wellord1(X1,X0))
          & r2_hidden(X2,k3_relat_1(X1)) )
      | r4_wellord1(X1,k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] :
              ~ ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,X2)),k2_wellord1(X1,X0))
                & r2_hidden(X2,k3_relat_1(X1)) )
          & ~ r4_wellord1(X1,k2_wellord1(X1,X0))
          & v2_wellord1(X1)
          & r1_tarski(X0,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',t64_wellord1)).

fof(f443,plain,
    ( ~ spl7_28
    | spl7_37 ),
    inference(avatar_contradiction_clause,[],[f442])).

fof(f442,plain,
    ( $false
    | ~ spl7_28
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f441,f90])).

fof(f441,plain,
    ( ~ v1_relat_1(k1_wellord2(sK1))
    | ~ spl7_28
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f439,f346])).

fof(f346,plain,
    ( ~ r2_hidden(sK6(sK0,k1_wellord2(sK1)),sK1)
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f345])).

fof(f345,plain,
    ( spl7_37
  <=> ~ r2_hidden(sK6(sK0,k1_wellord2(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f439,plain,
    ( r2_hidden(sK6(sK0,k1_wellord2(sK1)),sK1)
    | ~ v1_relat_1(k1_wellord2(sK1))
    | ~ spl7_28 ),
    inference(superposition,[],[f309,f137])).

fof(f419,plain,
    ( spl7_48
    | ~ spl7_0
    | ~ spl7_8
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f412,f320,f186,f149,f417])).

fof(f417,plain,
    ( spl7_48
  <=> k2_wellord2(k1_wellord2(sK0)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f320,plain,
    ( spl7_32
  <=> r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f412,plain,
    ( k2_wellord2(k1_wellord2(sK0)) = sK1
    | ~ spl7_0
    | ~ spl7_8
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f410,f150])).

fof(f410,plain,
    ( k2_wellord2(k1_wellord2(sK0)) = sK1
    | ~ v3_ordinal1(sK1)
    | ~ spl7_8
    | ~ spl7_32 ),
    inference(resolution,[],[f277,f321])).

fof(f321,plain,
    ( r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f320])).

fof(f326,plain,
    ( ~ spl7_2
    | spl7_31 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f324,f90])).

fof(f324,plain,
    ( ~ v1_relat_1(k1_wellord2(sK1))
    | ~ spl7_2
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f323,f157])).

fof(f157,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl7_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f323,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(k1_wellord2(sK1))
    | ~ spl7_31 ),
    inference(superposition,[],[f315,f137])).

fof(f315,plain,
    ( ~ r1_tarski(sK0,k3_relat_1(k1_wellord2(sK1)))
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f314])).

fof(f314,plain,
    ( spl7_31
  <=> ~ r1_tarski(sK0,k3_relat_1(k1_wellord2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f322,plain,
    ( spl7_28
    | ~ spl7_31
    | spl7_32
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f296,f282,f196,f320,f314,f308])).

fof(f296,plain,
    ( r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ r1_tarski(sK0,k3_relat_1(k1_wellord2(sK1)))
    | r2_hidden(sK6(sK0,k1_wellord2(sK1)),k3_relat_1(k1_wellord2(sK1)))
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f202,f283])).

fof(f202,plain,
    ( r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ r1_tarski(sK0,k3_relat_1(k1_wellord2(sK1)))
    | ~ v2_wellord1(k1_wellord2(sK1))
    | r2_hidden(sK6(sK0,k1_wellord2(sK1)),k3_relat_1(k1_wellord2(sK1)))
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f199,f90])).

fof(f199,plain,
    ( r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ r1_tarski(sK0,k3_relat_1(k1_wellord2(sK1)))
    | ~ v2_wellord1(k1_wellord2(sK1))
    | ~ v1_relat_1(k1_wellord2(sK1))
    | r2_hidden(sK6(sK0,k1_wellord2(sK1)),k3_relat_1(k1_wellord2(sK1)))
    | ~ spl7_10 ),
    inference(superposition,[],[f120,f197])).

fof(f120,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,k2_wellord1(X1,X0))
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK6(X0,X1),k3_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f284,plain,
    ( spl7_24
    | ~ spl7_12
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f269,f263,f214,f282])).

fof(f214,plain,
    ( spl7_12
  <=> v3_ordinal1(k2_wellord2(k1_wellord2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f263,plain,
    ( spl7_22
  <=> r1_tarski(sK1,k2_wellord2(k1_wellord2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f269,plain,
    ( v2_wellord1(k1_wellord2(sK1))
    | ~ spl7_12
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f268,f215])).

fof(f215,plain,
    ( v3_ordinal1(k2_wellord2(k1_wellord2(sK0)))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f214])).

fof(f268,plain,
    ( ~ v3_ordinal1(k2_wellord2(k1_wellord2(sK0)))
    | v2_wellord1(k1_wellord2(sK1))
    | ~ spl7_22 ),
    inference(resolution,[],[f264,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ v3_ordinal1(X0)
      | v2_wellord1(k1_wellord2(X1)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_wellord1(k1_wellord2(X1))
          | ~ r1_tarski(X1,X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( r1_tarski(X1,X0)
         => v2_wellord1(k1_wellord2(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',t9_wellord2)).

fof(f264,plain,
    ( r1_tarski(sK1,k2_wellord2(k1_wellord2(sK0)))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f263])).

fof(f265,plain,
    ( spl7_22
    | ~ spl7_0
    | ~ spl7_12
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f258,f254,f214,f149,f263])).

fof(f254,plain,
    ( spl7_20
  <=> r1_ordinal1(sK1,k2_wellord2(k1_wellord2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f258,plain,
    ( r1_tarski(sK1,k2_wellord2(k1_wellord2(sK0)))
    | ~ spl7_0
    | ~ spl7_12
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f257,f215])).

fof(f257,plain,
    ( r1_tarski(sK1,k2_wellord2(k1_wellord2(sK0)))
    | ~ v3_ordinal1(k2_wellord2(k1_wellord2(sK0)))
    | ~ spl7_0
    | ~ spl7_20 ),
    inference(resolution,[],[f255,f159])).

fof(f159,plain,
    ( ! [X0] :
        ( ~ r1_ordinal1(sK1,X0)
        | r1_tarski(sK1,X0)
        | ~ v3_ordinal1(X0) )
    | ~ spl7_0 ),
    inference(resolution,[],[f150,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',redefinition_r1_ordinal1)).

fof(f255,plain,
    ( r1_ordinal1(sK1,k2_wellord2(k1_wellord2(sK0)))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f254])).

fof(f256,plain,
    ( spl7_20
    | ~ spl7_0
    | spl7_5
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f248,f214,f168,f149,f254])).

fof(f168,plain,
    ( spl7_5
  <=> ~ r1_ordinal1(k2_wellord2(k1_wellord2(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f248,plain,
    ( r1_ordinal1(sK1,k2_wellord2(k1_wellord2(sK0)))
    | ~ spl7_0
    | ~ spl7_5
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f181,f215])).

fof(f181,plain,
    ( ~ v3_ordinal1(k2_wellord2(k1_wellord2(sK0)))
    | r1_ordinal1(sK1,k2_wellord2(k1_wellord2(sK0)))
    | ~ spl7_0
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f179,f150])).

fof(f179,plain,
    ( ~ v3_ordinal1(k2_wellord2(k1_wellord2(sK0)))
    | r1_ordinal1(sK1,k2_wellord2(k1_wellord2(sK0)))
    | ~ v3_ordinal1(sK1)
    | ~ spl7_5 ),
    inference(resolution,[],[f169,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',connectedness_r1_ordinal1)).

fof(f169,plain,
    ( ~ r1_ordinal1(k2_wellord2(k1_wellord2(sK0)),sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f168])).

fof(f247,plain,
    ( spl7_18
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f237,f230,f245])).

fof(f230,plain,
    ( spl7_16
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f237,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl7_16 ),
    inference(resolution,[],[f231,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',t3_subset)).

fof(f231,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f230])).

fof(f236,plain,(
    spl7_13 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f233,f90])).

fof(f233,plain,
    ( ~ v1_relat_1(k1_wellord2(sK0))
    | ~ spl7_13 ),
    inference(resolution,[],[f218,f94])).

fof(f94,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_wellord2(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_wellord2(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v3_ordinal1(k2_wellord2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',dt_k2_wellord2)).

fof(f218,plain,
    ( ~ v3_ordinal1(k2_wellord2(k1_wellord2(sK0)))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl7_13
  <=> ~ v3_ordinal1(k2_wellord2(k1_wellord2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f232,plain,
    ( spl7_16
    | ~ spl7_0 ),
    inference(avatar_split_clause,[],[f211,f149,f230])).

fof(f211,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl7_0 ),
    inference(subsumption_resolution,[],[f210,f150])).

fof(f210,plain,
    ( r1_tarski(sK1,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ spl7_0 ),
    inference(duplicate_literal_removal,[],[f205])).

fof(f205,plain,
    ( r1_tarski(sK1,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK1)
    | ~ spl7_0 ),
    inference(resolution,[],[f159,f144])).

fof(f144,plain,(
    ! [X0] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(condensation,[],[f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => r1_ordinal1(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',reflexivity_r1_ordinal1)).

fof(f225,plain,
    ( ~ spl7_13
    | ~ spl7_15
    | ~ spl7_0
    | spl7_5 ),
    inference(avatar_split_clause,[],[f180,f168,f149,f223,f217])).

fof(f223,plain,
    ( spl7_15
  <=> ~ r1_tarski(k2_wellord2(k1_wellord2(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f180,plain,
    ( ~ r1_tarski(k2_wellord2(k1_wellord2(sK0)),sK1)
    | ~ v3_ordinal1(k2_wellord2(k1_wellord2(sK0)))
    | ~ spl7_0
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f178,f150])).

fof(f178,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ r1_tarski(k2_wellord2(k1_wellord2(sK0)),sK1)
    | ~ v3_ordinal1(k2_wellord2(k1_wellord2(sK0)))
    | ~ spl7_5 ),
    inference(resolution,[],[f169,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f198,plain,
    ( spl7_10
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f161,f156,f196])).

fof(f161,plain,
    ( k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl7_2 ),
    inference(resolution,[],[f157,f122])).

fof(f188,plain,
    ( spl7_8
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f163,f156,f149,f186])).

fof(f163,plain,
    ( v2_wellord1(k1_wellord2(sK0))
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f162,f150])).

fof(f162,plain,
    ( ~ v3_ordinal1(sK1)
    | v2_wellord1(k1_wellord2(sK0))
    | ~ spl7_2 ),
    inference(resolution,[],[f157,f102])).

fof(f170,plain,(
    ~ spl7_5 ),
    inference(avatar_split_clause,[],[f88,f168])).

fof(f88,plain,(
    ~ r1_ordinal1(k2_wellord2(k1_wellord2(sK0)),sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ? [X0,X1] :
      ( ~ r1_ordinal1(k2_wellord2(k1_wellord2(X0)),X1)
      & r1_tarski(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ? [X0,X1] :
      ( ~ r1_ordinal1(k2_wellord2(k1_wellord2(X0)),X1)
      & r1_tarski(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v3_ordinal1(X1)
       => ( r1_tarski(X0,X1)
         => r1_ordinal1(k2_wellord2(k1_wellord2(X0)),X1) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r1_tarski(X0,X1)
       => r1_ordinal1(k2_wellord2(k1_wellord2(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',t17_wellord2)).

fof(f158,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f87,f156])).

fof(f87,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f151,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f86,f149])).

fof(f86,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
