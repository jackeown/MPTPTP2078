%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:47 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 237 expanded)
%              Number of leaves         :   42 ( 104 expanded)
%              Depth                    :    9
%              Number of atoms          :  411 ( 666 expanded)
%              Number of equality atoms :   70 ( 122 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1017,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f110,f152,f204,f205,f206,f217,f256,f257,f276,f339,f361,f376,f399,f407,f562,f681,f753,f917,f935,f1016])).

fof(f1016,plain,
    ( spl5_35
    | ~ spl5_87 ),
    inference(avatar_contradiction_clause,[],[f1015])).

fof(f1015,plain,
    ( $false
    | spl5_35
    | ~ spl5_87 ),
    inference(subsumption_resolution,[],[f949,f98])).

fof(f98,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f949,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl5_35
    | ~ spl5_87 ),
    inference(backward_demodulation,[],[f374,f934])).

fof(f934,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_87 ),
    inference(avatar_component_clause,[],[f932])).

fof(f932,plain,
    ( spl5_87
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).

fof(f374,plain,
    ( ~ r1_xboole_0(sK2,sK2)
    | spl5_35 ),
    inference(avatar_component_clause,[],[f372])).

fof(f372,plain,
    ( spl5_35
  <=> r1_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f935,plain,
    ( spl5_87
    | ~ spl5_71
    | ~ spl5_85 ),
    inference(avatar_split_clause,[],[f924,f914,f750,f932])).

fof(f750,plain,
    ( spl5_71
  <=> sK2 = k7_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).

fof(f914,plain,
    ( spl5_85
  <=> k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).

fof(f924,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_71
    | ~ spl5_85 ),
    inference(backward_demodulation,[],[f752,f916])).

fof(f916,plain,
    ( k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0)
    | ~ spl5_85 ),
    inference(avatar_component_clause,[],[f914])).

fof(f752,plain,
    ( sK2 = k7_relat_1(sK2,k1_xboole_0)
    | ~ spl5_71 ),
    inference(avatar_component_clause,[],[f750])).

fof(f917,plain,
    ( spl5_85
    | ~ spl5_22
    | ~ spl5_71 ),
    inference(avatar_split_clause,[],[f908,f750,f253,f914])).

fof(f253,plain,
    ( spl5_22
  <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f908,plain,
    ( k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0)
    | ~ spl5_22
    | ~ spl5_71 ),
    inference(backward_demodulation,[],[f255,f752])).

fof(f255,plain,
    ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,k1_xboole_0),k1_xboole_0)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f253])).

fof(f753,plain,
    ( spl5_71
    | ~ spl5_20
    | ~ spl5_37 ),
    inference(avatar_split_clause,[],[f733,f392,f242,f750])).

fof(f242,plain,
    ( spl5_20
  <=> sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f392,plain,
    ( spl5_37
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f733,plain,
    ( sK2 = k7_relat_1(sK2,k1_xboole_0)
    | ~ spl5_20
    | ~ spl5_37 ),
    inference(backward_demodulation,[],[f244,f394])).

fof(f394,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f392])).

fof(f244,plain,
    ( sK2 = k7_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f242])).

fof(f681,plain,
    ( spl5_37
    | spl5_54 ),
    inference(avatar_split_clause,[],[f678,f559,f392])).

fof(f559,plain,
    ( spl5_54
  <=> r2_hidden(sK3(k1_relat_1(sK2)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f678,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | spl5_54 ),
    inference(resolution,[],[f561,f74])).

fof(f74,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f561,plain,
    ( ~ r2_hidden(sK3(k1_relat_1(sK2)),k1_relat_1(sK2))
    | spl5_54 ),
    inference(avatar_component_clause,[],[f559])).

fof(f562,plain,
    ( ~ spl5_54
    | ~ spl5_24
    | spl5_39 ),
    inference(avatar_split_clause,[],[f553,f403,f273,f559])).

fof(f273,plain,
    ( spl5_24
  <=> r1_tarski(k1_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f403,plain,
    ( spl5_39
  <=> r2_hidden(sK3(k1_relat_1(sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f553,plain,
    ( ~ r2_hidden(sK3(k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl5_24
    | spl5_39 ),
    inference(unit_resulting_resolution,[],[f275,f405,f86])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f58,f59])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f405,plain,
    ( ~ r2_hidden(sK3(k1_relat_1(sK2)),sK1)
    | spl5_39 ),
    inference(avatar_component_clause,[],[f403])).

fof(f275,plain,
    ( r1_tarski(k1_relat_1(sK2),sK1)
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f273])).

fof(f407,plain,
    ( ~ spl5_39
    | spl5_38 ),
    inference(avatar_split_clause,[],[f401,f396,f403])).

fof(f396,plain,
    ( spl5_38
  <=> m1_subset_1(sK3(k1_relat_1(sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f401,plain,
    ( ~ r2_hidden(sK3(k1_relat_1(sK2)),sK1)
    | spl5_38 ),
    inference(resolution,[],[f398,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f398,plain,
    ( ~ m1_subset_1(sK3(k1_relat_1(sK2)),sK1)
    | spl5_38 ),
    inference(avatar_component_clause,[],[f396])).

fof(f399,plain,
    ( spl5_37
    | ~ spl5_38
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f388,f195,f396,f392])).

fof(f195,plain,
    ( spl5_14
  <=> k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f388,plain,
    ( ~ m1_subset_1(sK3(k1_relat_1(sK2)),sK1)
    | k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl5_14 ),
    inference(resolution,[],[f377,f74])).

fof(f377,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relat_1(sK2))
        | ~ m1_subset_1(X3,sK1) )
    | ~ spl5_14 ),
    inference(backward_demodulation,[],[f67,f197])).

fof(f197,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f195])).

fof(f67,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
        | ~ m1_subset_1(X3,sK1) )
    & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f50,f49,f48])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                    | ~ m1_subset_1(X3,X1) )
                & k1_xboole_0 != k2_relset_1(X1,X0,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,sK0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,sK0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( ~ r2_hidden(X3,k1_relset_1(X1,sK0,X2))
                | ~ m1_subset_1(X3,X1) )
            & k1_xboole_0 != k2_relset_1(X1,sK0,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,X2))
              | ~ m1_subset_1(X3,sK1) )
          & k1_xboole_0 != k2_relset_1(sK1,sK0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,X2))
            | ~ m1_subset_1(X3,sK1) )
        & k1_xboole_0 != k2_relset_1(sK1,sK0,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) )
   => ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
          | ~ m1_subset_1(X3,sK1) )
      & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                    & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                  & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

fof(f376,plain,
    ( ~ spl5_35
    | spl5_33 ),
    inference(avatar_split_clause,[],[f362,f357,f372])).

fof(f357,plain,
    ( spl5_33
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f362,plain,
    ( ~ r1_xboole_0(sK2,sK2)
    | spl5_33 ),
    inference(unit_resulting_resolution,[],[f100,f359,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f359,plain,
    ( ~ v1_xboole_0(sK2)
    | spl5_33 ),
    inference(avatar_component_clause,[],[f357])).

fof(f100,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f361,plain,
    ( ~ spl5_33
    | spl5_30 ),
    inference(avatar_split_clause,[],[f348,f336,f357])).

fof(f336,plain,
    ( spl5_30
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f348,plain,
    ( ~ v1_xboole_0(sK2)
    | spl5_30 ),
    inference(resolution,[],[f338,f71])).

fof(f71,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

fof(f338,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl5_30 ),
    inference(avatar_component_clause,[],[f336])).

fof(f339,plain,
    ( ~ spl5_30
    | spl5_8
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f333,f190,f149,f336])).

fof(f149,plain,
    ( spl5_8
  <=> v1_xboole_0(k2_relset_1(sK1,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f190,plain,
    ( spl5_13
  <=> k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f333,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl5_8
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f151,f192])).

fof(f192,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f190])).

fof(f151,plain,
    ( ~ v1_xboole_0(k2_relset_1(sK1,sK0,sK2))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f149])).

fof(f276,plain,
    ( spl5_24
    | ~ spl5_11
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f269,f200,f180,f273])).

fof(f180,plain,
    ( spl5_11
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f200,plain,
    ( spl5_15
  <=> v4_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f269,plain,
    ( r1_tarski(k1_relat_1(sK2),sK1)
    | ~ spl5_11
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f182,f202,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f202,plain,
    ( v4_relat_1(sK2,sK1)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f200])).

fof(f182,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f180])).

fof(f257,plain,
    ( spl5_20
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f240,f180,f242])).

fof(f240,plain,
    ( sK2 = k7_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl5_11 ),
    inference(resolution,[],[f182,f72])).

fof(f72,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f256,plain,
    ( spl5_22
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f231,f180,f253])).

fof(f231,plain,
    ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,k1_xboole_0),k1_xboole_0)
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f98,f182,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

fof(f217,plain,
    ( spl5_11
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f216,f107,f180])).

fof(f107,plain,
    ( spl5_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f216,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f178,f75])).

fof(f75,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f178,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | ~ spl5_2 ),
    inference(resolution,[],[f109,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f109,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f206,plain,
    ( spl5_13
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f175,f107,f190])).

fof(f175,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)
    | ~ spl5_2 ),
    inference(resolution,[],[f109,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f205,plain,
    ( spl5_14
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f174,f107,f195])).

fof(f174,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl5_2 ),
    inference(resolution,[],[f109,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f204,plain,
    ( spl5_15
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f173,f107,f200])).

fof(f173,plain,
    ( v4_relat_1(sK2,sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f109,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f152,plain,
    ( ~ spl5_8
    | spl5_1 ),
    inference(avatar_split_clause,[],[f140,f102,f149])).

fof(f102,plain,
    ( spl5_1
  <=> k1_xboole_0 = k2_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f140,plain,
    ( ~ v1_xboole_0(k2_relset_1(sK1,sK0,sK2))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f104,f70])).

fof(f70,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f104,plain,
    ( k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f110,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f65,f107])).

fof(f65,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f105,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f66,f102])).

fof(f66,plain,(
    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:28:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (29756)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (29763)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (29753)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (29758)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (29776)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (29754)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (29757)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.35/0.54  % (29777)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.35/0.54  % (29774)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.35/0.54  % (29778)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.35/0.54  % (29755)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.35/0.54  % (29752)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.35/0.54  % (29782)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.35/0.54  % (29781)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.35/0.54  % (29766)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.35/0.54  % (29779)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.35/0.55  % (29772)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.35/0.55  % (29759)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.35/0.55  % (29768)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.35/0.55  % (29762)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.35/0.55  % (29773)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.35/0.55  % (29771)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.35/0.55  % (29775)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.35/0.55  % (29767)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.35/0.55  % (29765)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.35/0.55  % (29760)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.52/0.56  % (29761)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.52/0.56  % (29760)Refutation not found, incomplete strategy% (29760)------------------------------
% 1.52/0.56  % (29760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (29760)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.56  % (29760)Memory used [KB]: 10746
% 1.52/0.56  % (29760)Time elapsed: 0.148 s
% 1.52/0.56  % (29760)------------------------------
% 1.52/0.56  % (29760)------------------------------
% 1.52/0.56  % (29764)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.52/0.56  % (29770)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.52/0.56  % (29780)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.52/0.56  % (29778)Refutation found. Thanks to Tanya!
% 1.52/0.56  % SZS status Theorem for theBenchmark
% 1.52/0.58  % SZS output start Proof for theBenchmark
% 1.52/0.58  fof(f1017,plain,(
% 1.52/0.58    $false),
% 1.52/0.58    inference(avatar_sat_refutation,[],[f105,f110,f152,f204,f205,f206,f217,f256,f257,f276,f339,f361,f376,f399,f407,f562,f681,f753,f917,f935,f1016])).
% 1.52/0.59  fof(f1016,plain,(
% 1.52/0.59    spl5_35 | ~spl5_87),
% 1.52/0.59    inference(avatar_contradiction_clause,[],[f1015])).
% 1.52/0.59  fof(f1015,plain,(
% 1.52/0.59    $false | (spl5_35 | ~spl5_87)),
% 1.52/0.59    inference(subsumption_resolution,[],[f949,f98])).
% 1.52/0.59  fof(f98,plain,(
% 1.52/0.59    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.52/0.59    inference(equality_resolution,[],[f68])).
% 1.52/0.59  fof(f68,plain,(
% 1.52/0.59    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 1.52/0.59    inference(cnf_transformation,[],[f28])).
% 1.52/0.59  fof(f28,plain,(
% 1.52/0.59    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.52/0.59    inference(ennf_transformation,[],[f8])).
% 1.52/0.59  fof(f8,axiom,(
% 1.52/0.59    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.52/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.52/0.59  fof(f949,plain,(
% 1.52/0.59    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | (spl5_35 | ~spl5_87)),
% 1.52/0.59    inference(backward_demodulation,[],[f374,f934])).
% 1.52/0.59  fof(f934,plain,(
% 1.52/0.59    k1_xboole_0 = sK2 | ~spl5_87),
% 1.52/0.59    inference(avatar_component_clause,[],[f932])).
% 1.52/0.59  fof(f932,plain,(
% 1.52/0.59    spl5_87 <=> k1_xboole_0 = sK2),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).
% 1.52/0.59  fof(f374,plain,(
% 1.52/0.59    ~r1_xboole_0(sK2,sK2) | spl5_35),
% 1.52/0.59    inference(avatar_component_clause,[],[f372])).
% 1.52/0.59  fof(f372,plain,(
% 1.52/0.59    spl5_35 <=> r1_xboole_0(sK2,sK2)),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 1.52/0.59  fof(f935,plain,(
% 1.52/0.59    spl5_87 | ~spl5_71 | ~spl5_85),
% 1.52/0.59    inference(avatar_split_clause,[],[f924,f914,f750,f932])).
% 1.52/0.59  fof(f750,plain,(
% 1.52/0.59    spl5_71 <=> sK2 = k7_relat_1(sK2,k1_xboole_0)),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).
% 1.52/0.59  fof(f914,plain,(
% 1.52/0.59    spl5_85 <=> k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0)),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).
% 1.52/0.59  fof(f924,plain,(
% 1.52/0.59    k1_xboole_0 = sK2 | (~spl5_71 | ~spl5_85)),
% 1.52/0.59    inference(backward_demodulation,[],[f752,f916])).
% 1.52/0.59  fof(f916,plain,(
% 1.52/0.59    k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0) | ~spl5_85),
% 1.52/0.59    inference(avatar_component_clause,[],[f914])).
% 1.52/0.59  fof(f752,plain,(
% 1.52/0.59    sK2 = k7_relat_1(sK2,k1_xboole_0) | ~spl5_71),
% 1.52/0.59    inference(avatar_component_clause,[],[f750])).
% 1.52/0.59  fof(f917,plain,(
% 1.52/0.59    spl5_85 | ~spl5_22 | ~spl5_71),
% 1.52/0.59    inference(avatar_split_clause,[],[f908,f750,f253,f914])).
% 1.52/0.59  fof(f253,plain,(
% 1.52/0.59    spl5_22 <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,k1_xboole_0),k1_xboole_0)),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 1.52/0.59  fof(f908,plain,(
% 1.52/0.59    k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0) | (~spl5_22 | ~spl5_71)),
% 1.52/0.59    inference(backward_demodulation,[],[f255,f752])).
% 1.52/0.59  fof(f255,plain,(
% 1.52/0.59    k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,k1_xboole_0),k1_xboole_0) | ~spl5_22),
% 1.52/0.59    inference(avatar_component_clause,[],[f253])).
% 1.52/0.59  fof(f753,plain,(
% 1.52/0.59    spl5_71 | ~spl5_20 | ~spl5_37),
% 1.52/0.59    inference(avatar_split_clause,[],[f733,f392,f242,f750])).
% 1.52/0.59  fof(f242,plain,(
% 1.52/0.59    spl5_20 <=> sK2 = k7_relat_1(sK2,k1_relat_1(sK2))),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.52/0.59  fof(f392,plain,(
% 1.52/0.59    spl5_37 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 1.52/0.59  fof(f733,plain,(
% 1.52/0.59    sK2 = k7_relat_1(sK2,k1_xboole_0) | (~spl5_20 | ~spl5_37)),
% 1.52/0.59    inference(backward_demodulation,[],[f244,f394])).
% 1.52/0.59  fof(f394,plain,(
% 1.52/0.59    k1_xboole_0 = k1_relat_1(sK2) | ~spl5_37),
% 1.52/0.59    inference(avatar_component_clause,[],[f392])).
% 1.52/0.59  fof(f244,plain,(
% 1.52/0.59    sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) | ~spl5_20),
% 1.52/0.59    inference(avatar_component_clause,[],[f242])).
% 1.52/0.59  fof(f681,plain,(
% 1.52/0.59    spl5_37 | spl5_54),
% 1.52/0.59    inference(avatar_split_clause,[],[f678,f559,f392])).
% 1.52/0.59  fof(f559,plain,(
% 1.52/0.59    spl5_54 <=> r2_hidden(sK3(k1_relat_1(sK2)),k1_relat_1(sK2))),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).
% 1.52/0.59  fof(f678,plain,(
% 1.52/0.59    k1_xboole_0 = k1_relat_1(sK2) | spl5_54),
% 1.52/0.59    inference(resolution,[],[f561,f74])).
% 1.52/0.59  fof(f74,plain,(
% 1.52/0.59    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.52/0.59    inference(cnf_transformation,[],[f53])).
% 1.52/0.59  fof(f53,plain,(
% 1.52/0.59    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 1.52/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f52])).
% 1.52/0.59  fof(f52,plain,(
% 1.52/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.52/0.59    introduced(choice_axiom,[])).
% 1.52/0.59  fof(f33,plain,(
% 1.52/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.52/0.59    inference(ennf_transformation,[],[f5])).
% 1.52/0.59  fof(f5,axiom,(
% 1.52/0.59    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.52/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.52/0.59  fof(f561,plain,(
% 1.52/0.59    ~r2_hidden(sK3(k1_relat_1(sK2)),k1_relat_1(sK2)) | spl5_54),
% 1.52/0.59    inference(avatar_component_clause,[],[f559])).
% 1.52/0.59  fof(f562,plain,(
% 1.52/0.59    ~spl5_54 | ~spl5_24 | spl5_39),
% 1.52/0.59    inference(avatar_split_clause,[],[f553,f403,f273,f559])).
% 1.52/0.59  fof(f273,plain,(
% 1.52/0.59    spl5_24 <=> r1_tarski(k1_relat_1(sK2),sK1)),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 1.52/0.59  fof(f403,plain,(
% 1.52/0.59    spl5_39 <=> r2_hidden(sK3(k1_relat_1(sK2)),sK1)),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 1.52/0.59  fof(f553,plain,(
% 1.52/0.59    ~r2_hidden(sK3(k1_relat_1(sK2)),k1_relat_1(sK2)) | (~spl5_24 | spl5_39)),
% 1.52/0.59    inference(unit_resulting_resolution,[],[f275,f405,f86])).
% 1.52/0.59  fof(f86,plain,(
% 1.52/0.59    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.52/0.59    inference(cnf_transformation,[],[f60])).
% 1.52/0.59  fof(f60,plain,(
% 1.52/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f58,f59])).
% 1.52/0.59  fof(f59,plain,(
% 1.52/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.52/0.59    introduced(choice_axiom,[])).
% 1.52/0.59  fof(f58,plain,(
% 1.52/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.59    inference(rectify,[],[f57])).
% 1.52/0.59  fof(f57,plain,(
% 1.52/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.59    inference(nnf_transformation,[],[f41])).
% 1.52/0.59  fof(f41,plain,(
% 1.52/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.52/0.59    inference(ennf_transformation,[],[f1])).
% 1.52/0.59  fof(f1,axiom,(
% 1.52/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.52/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.52/0.59  fof(f405,plain,(
% 1.52/0.59    ~r2_hidden(sK3(k1_relat_1(sK2)),sK1) | spl5_39),
% 1.52/0.59    inference(avatar_component_clause,[],[f403])).
% 1.52/0.59  fof(f275,plain,(
% 1.52/0.59    r1_tarski(k1_relat_1(sK2),sK1) | ~spl5_24),
% 1.52/0.59    inference(avatar_component_clause,[],[f273])).
% 1.52/0.59  fof(f407,plain,(
% 1.52/0.59    ~spl5_39 | spl5_38),
% 1.52/0.59    inference(avatar_split_clause,[],[f401,f396,f403])).
% 1.52/0.59  fof(f396,plain,(
% 1.52/0.59    spl5_38 <=> m1_subset_1(sK3(k1_relat_1(sK2)),sK1)),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 1.52/0.59  fof(f401,plain,(
% 1.52/0.59    ~r2_hidden(sK3(k1_relat_1(sK2)),sK1) | spl5_38),
% 1.52/0.59    inference(resolution,[],[f398,f80])).
% 1.52/0.59  fof(f80,plain,(
% 1.52/0.59    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.52/0.59    inference(cnf_transformation,[],[f37])).
% 1.52/0.59  fof(f37,plain,(
% 1.52/0.59    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.52/0.59    inference(ennf_transformation,[],[f10])).
% 1.52/0.59  fof(f10,axiom,(
% 1.52/0.59    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.52/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.52/0.59  fof(f398,plain,(
% 1.52/0.59    ~m1_subset_1(sK3(k1_relat_1(sK2)),sK1) | spl5_38),
% 1.52/0.59    inference(avatar_component_clause,[],[f396])).
% 1.52/0.59  fof(f399,plain,(
% 1.52/0.59    spl5_37 | ~spl5_38 | ~spl5_14),
% 1.52/0.59    inference(avatar_split_clause,[],[f388,f195,f396,f392])).
% 1.52/0.59  fof(f195,plain,(
% 1.52/0.59    spl5_14 <=> k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.52/0.59  fof(f388,plain,(
% 1.52/0.59    ~m1_subset_1(sK3(k1_relat_1(sK2)),sK1) | k1_xboole_0 = k1_relat_1(sK2) | ~spl5_14),
% 1.52/0.59    inference(resolution,[],[f377,f74])).
% 1.52/0.59  fof(f377,plain,(
% 1.52/0.59    ( ! [X3] : (~r2_hidden(X3,k1_relat_1(sK2)) | ~m1_subset_1(X3,sK1)) ) | ~spl5_14),
% 1.52/0.59    inference(backward_demodulation,[],[f67,f197])).
% 1.52/0.59  fof(f197,plain,(
% 1.52/0.59    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) | ~spl5_14),
% 1.52/0.59    inference(avatar_component_clause,[],[f195])).
% 1.52/0.59  fof(f67,plain,(
% 1.52/0.59    ( ! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) )),
% 1.52/0.59    inference(cnf_transformation,[],[f51])).
% 1.52/0.59  fof(f51,plain,(
% 1.52/0.59    ((! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 1.52/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f50,f49,f48])).
% 1.52/0.59  fof(f48,plain,(
% 1.52/0.59    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,sK0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,sK0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 1.52/0.59    introduced(choice_axiom,[])).
% 1.52/0.59  fof(f49,plain,(
% 1.52/0.59    ? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,sK0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,sK0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))) & ~v1_xboole_0(X1)) => (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,X2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) & ~v1_xboole_0(sK1))),
% 1.52/0.59    introduced(choice_axiom,[])).
% 1.52/0.59  fof(f50,plain,(
% 1.52/0.59    ? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,X2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) => (! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 1.52/0.59    introduced(choice_axiom,[])).
% 1.52/0.59  fof(f27,plain,(
% 1.52/0.59    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.52/0.59    inference(flattening,[],[f26])).
% 1.52/0.59  fof(f26,plain,(
% 1.52/0.59    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.52/0.59    inference(ennf_transformation,[],[f24])).
% 1.52/0.59  fof(f24,negated_conjecture,(
% 1.52/0.59    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 1.52/0.59    inference(negated_conjecture,[],[f23])).
% 1.52/0.59  fof(f23,conjecture,(
% 1.52/0.59    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 1.52/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).
% 1.52/0.59  fof(f376,plain,(
% 1.52/0.59    ~spl5_35 | spl5_33),
% 1.52/0.59    inference(avatar_split_clause,[],[f362,f357,f372])).
% 1.52/0.59  fof(f357,plain,(
% 1.52/0.59    spl5_33 <=> v1_xboole_0(sK2)),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 1.52/0.59  fof(f362,plain,(
% 1.52/0.59    ~r1_xboole_0(sK2,sK2) | spl5_33),
% 1.52/0.59    inference(unit_resulting_resolution,[],[f100,f359,f77])).
% 1.52/0.59  fof(f77,plain,(
% 1.52/0.59    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 1.52/0.59    inference(cnf_transformation,[],[f35])).
% 1.52/0.59  fof(f35,plain,(
% 1.52/0.59    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.52/0.59    inference(flattening,[],[f34])).
% 1.52/0.59  fof(f34,plain,(
% 1.52/0.59    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.52/0.59    inference(ennf_transformation,[],[f9])).
% 1.52/0.59  fof(f9,axiom,(
% 1.52/0.59    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.52/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 1.52/0.59  fof(f359,plain,(
% 1.52/0.59    ~v1_xboole_0(sK2) | spl5_33),
% 1.52/0.59    inference(avatar_component_clause,[],[f357])).
% 1.52/0.59  fof(f100,plain,(
% 1.52/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.52/0.59    inference(equality_resolution,[],[f83])).
% 1.52/0.59  fof(f83,plain,(
% 1.52/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.52/0.59    inference(cnf_transformation,[],[f56])).
% 1.52/0.59  fof(f56,plain,(
% 1.52/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.52/0.59    inference(flattening,[],[f55])).
% 1.52/0.59  fof(f55,plain,(
% 1.52/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.52/0.59    inference(nnf_transformation,[],[f6])).
% 1.52/0.59  fof(f6,axiom,(
% 1.52/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.52/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.52/0.59  fof(f361,plain,(
% 1.52/0.59    ~spl5_33 | spl5_30),
% 1.52/0.59    inference(avatar_split_clause,[],[f348,f336,f357])).
% 1.52/0.59  fof(f336,plain,(
% 1.52/0.59    spl5_30 <=> v1_xboole_0(k2_relat_1(sK2))),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 1.52/0.59  fof(f348,plain,(
% 1.52/0.59    ~v1_xboole_0(sK2) | spl5_30),
% 1.52/0.59    inference(resolution,[],[f338,f71])).
% 1.52/0.59  fof(f71,plain,(
% 1.52/0.59    ( ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.52/0.59    inference(cnf_transformation,[],[f30])).
% 1.52/0.59  fof(f30,plain,(
% 1.52/0.59    ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 1.52/0.59    inference(ennf_transformation,[],[f15])).
% 1.52/0.59  fof(f15,axiom,(
% 1.52/0.59    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k2_relat_1(X0)))),
% 1.52/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).
% 1.52/0.59  fof(f338,plain,(
% 1.52/0.59    ~v1_xboole_0(k2_relat_1(sK2)) | spl5_30),
% 1.52/0.59    inference(avatar_component_clause,[],[f336])).
% 1.52/0.59  fof(f339,plain,(
% 1.52/0.59    ~spl5_30 | spl5_8 | ~spl5_13),
% 1.52/0.59    inference(avatar_split_clause,[],[f333,f190,f149,f336])).
% 1.52/0.59  fof(f149,plain,(
% 1.52/0.59    spl5_8 <=> v1_xboole_0(k2_relset_1(sK1,sK0,sK2))),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.52/0.59  fof(f190,plain,(
% 1.52/0.59    spl5_13 <=> k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.52/0.59  fof(f333,plain,(
% 1.52/0.59    ~v1_xboole_0(k2_relat_1(sK2)) | (spl5_8 | ~spl5_13)),
% 1.52/0.59    inference(backward_demodulation,[],[f151,f192])).
% 1.52/0.59  fof(f192,plain,(
% 1.52/0.59    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) | ~spl5_13),
% 1.52/0.59    inference(avatar_component_clause,[],[f190])).
% 1.52/0.59  fof(f151,plain,(
% 1.52/0.59    ~v1_xboole_0(k2_relset_1(sK1,sK0,sK2)) | spl5_8),
% 1.52/0.59    inference(avatar_component_clause,[],[f149])).
% 1.52/0.59  fof(f276,plain,(
% 1.52/0.59    spl5_24 | ~spl5_11 | ~spl5_15),
% 1.52/0.59    inference(avatar_split_clause,[],[f269,f200,f180,f273])).
% 1.52/0.59  fof(f180,plain,(
% 1.52/0.59    spl5_11 <=> v1_relat_1(sK2)),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.52/0.59  fof(f200,plain,(
% 1.52/0.59    spl5_15 <=> v4_relat_1(sK2,sK1)),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.52/0.59  fof(f269,plain,(
% 1.52/0.59    r1_tarski(k1_relat_1(sK2),sK1) | (~spl5_11 | ~spl5_15)),
% 1.52/0.59    inference(unit_resulting_resolution,[],[f182,f202,f78])).
% 1.52/0.59  fof(f78,plain,(
% 1.52/0.59    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.52/0.59    inference(cnf_transformation,[],[f54])).
% 1.52/0.59  fof(f54,plain,(
% 1.52/0.59    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.52/0.59    inference(nnf_transformation,[],[f36])).
% 1.52/0.59  fof(f36,plain,(
% 1.52/0.59    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.52/0.59    inference(ennf_transformation,[],[f14])).
% 1.52/0.59  fof(f14,axiom,(
% 1.52/0.59    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.52/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.52/0.59  fof(f202,plain,(
% 1.52/0.59    v4_relat_1(sK2,sK1) | ~spl5_15),
% 1.52/0.59    inference(avatar_component_clause,[],[f200])).
% 1.52/0.59  fof(f182,plain,(
% 1.52/0.59    v1_relat_1(sK2) | ~spl5_11),
% 1.52/0.59    inference(avatar_component_clause,[],[f180])).
% 1.52/0.59  fof(f257,plain,(
% 1.52/0.59    spl5_20 | ~spl5_11),
% 1.52/0.59    inference(avatar_split_clause,[],[f240,f180,f242])).
% 1.52/0.59  fof(f240,plain,(
% 1.52/0.59    sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) | ~spl5_11),
% 1.52/0.59    inference(resolution,[],[f182,f72])).
% 1.52/0.59  fof(f72,plain,(
% 1.52/0.59    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 1.52/0.59    inference(cnf_transformation,[],[f31])).
% 1.52/0.59  fof(f31,plain,(
% 1.52/0.59    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.52/0.59    inference(ennf_transformation,[],[f19])).
% 1.52/0.59  fof(f19,axiom,(
% 1.52/0.59    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 1.52/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 1.52/0.59  fof(f256,plain,(
% 1.52/0.59    spl5_22 | ~spl5_11),
% 1.52/0.59    inference(avatar_split_clause,[],[f231,f180,f253])).
% 1.52/0.59  fof(f231,plain,(
% 1.52/0.59    k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,k1_xboole_0),k1_xboole_0) | ~spl5_11),
% 1.52/0.59    inference(unit_resulting_resolution,[],[f98,f182,f93])).
% 1.52/0.59  fof(f93,plain,(
% 1.52/0.59    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 1.52/0.59    inference(cnf_transformation,[],[f43])).
% 1.52/0.59  fof(f43,plain,(
% 1.52/0.59    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 1.52/0.59    inference(flattening,[],[f42])).
% 1.52/0.59  fof(f42,plain,(
% 1.52/0.59    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.52/0.59    inference(ennf_transformation,[],[f17])).
% 1.52/0.59  fof(f17,axiom,(
% 1.52/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 1.52/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).
% 1.52/0.59  fof(f217,plain,(
% 1.52/0.59    spl5_11 | ~spl5_2),
% 1.52/0.59    inference(avatar_split_clause,[],[f216,f107,f180])).
% 1.52/0.59  fof(f107,plain,(
% 1.52/0.59    spl5_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.52/0.59  fof(f216,plain,(
% 1.52/0.59    v1_relat_1(sK2) | ~spl5_2),
% 1.52/0.59    inference(subsumption_resolution,[],[f178,f75])).
% 1.52/0.59  fof(f75,plain,(
% 1.52/0.59    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.52/0.59    inference(cnf_transformation,[],[f16])).
% 1.52/0.59  fof(f16,axiom,(
% 1.52/0.59    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.52/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.52/0.59  fof(f178,plain,(
% 1.52/0.59    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | ~spl5_2),
% 1.52/0.59    inference(resolution,[],[f109,f73])).
% 1.52/0.59  fof(f73,plain,(
% 1.52/0.59    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.52/0.59    inference(cnf_transformation,[],[f32])).
% 1.52/0.59  fof(f32,plain,(
% 1.52/0.59    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.52/0.59    inference(ennf_transformation,[],[f13])).
% 1.52/0.59  fof(f13,axiom,(
% 1.52/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.52/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.52/0.59  fof(f109,plain,(
% 1.52/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl5_2),
% 1.52/0.59    inference(avatar_component_clause,[],[f107])).
% 1.52/0.59  fof(f206,plain,(
% 1.52/0.59    spl5_13 | ~spl5_2),
% 1.52/0.59    inference(avatar_split_clause,[],[f175,f107,f190])).
% 1.52/0.59  fof(f175,plain,(
% 1.52/0.59    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) | ~spl5_2),
% 1.52/0.59    inference(resolution,[],[f109,f94])).
% 1.52/0.59  fof(f94,plain,(
% 1.52/0.59    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.52/0.59    inference(cnf_transformation,[],[f44])).
% 1.52/0.59  fof(f44,plain,(
% 1.52/0.59    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.59    inference(ennf_transformation,[],[f22])).
% 1.52/0.59  fof(f22,axiom,(
% 1.52/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.52/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.52/0.59  fof(f205,plain,(
% 1.52/0.59    spl5_14 | ~spl5_2),
% 1.52/0.59    inference(avatar_split_clause,[],[f174,f107,f195])).
% 1.52/0.59  fof(f174,plain,(
% 1.52/0.59    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) | ~spl5_2),
% 1.52/0.59    inference(resolution,[],[f109,f95])).
% 1.52/0.59  fof(f95,plain,(
% 1.52/0.59    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.52/0.59    inference(cnf_transformation,[],[f45])).
% 1.52/0.59  fof(f45,plain,(
% 1.52/0.59    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.59    inference(ennf_transformation,[],[f21])).
% 1.52/0.59  fof(f21,axiom,(
% 1.52/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.52/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.52/0.59  fof(f204,plain,(
% 1.52/0.59    spl5_15 | ~spl5_2),
% 1.52/0.59    inference(avatar_split_clause,[],[f173,f107,f200])).
% 1.52/0.59  fof(f173,plain,(
% 1.52/0.59    v4_relat_1(sK2,sK1) | ~spl5_2),
% 1.52/0.59    inference(resolution,[],[f109,f96])).
% 1.52/0.59  fof(f96,plain,(
% 1.52/0.59    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.52/0.59    inference(cnf_transformation,[],[f46])).
% 1.52/0.59  fof(f46,plain,(
% 1.52/0.59    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.59    inference(ennf_transformation,[],[f25])).
% 1.52/0.59  fof(f25,plain,(
% 1.52/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.52/0.59    inference(pure_predicate_removal,[],[f20])).
% 1.52/0.59  fof(f20,axiom,(
% 1.52/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.52/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.52/0.59  fof(f152,plain,(
% 1.52/0.59    ~spl5_8 | spl5_1),
% 1.52/0.59    inference(avatar_split_clause,[],[f140,f102,f149])).
% 1.52/0.59  fof(f102,plain,(
% 1.52/0.59    spl5_1 <=> k1_xboole_0 = k2_relset_1(sK1,sK0,sK2)),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.52/0.59  fof(f140,plain,(
% 1.52/0.59    ~v1_xboole_0(k2_relset_1(sK1,sK0,sK2)) | spl5_1),
% 1.52/0.59    inference(unit_resulting_resolution,[],[f104,f70])).
% 1.52/0.59  fof(f70,plain,(
% 1.52/0.59    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.52/0.59    inference(cnf_transformation,[],[f29])).
% 1.52/0.59  fof(f29,plain,(
% 1.52/0.59    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.52/0.59    inference(ennf_transformation,[],[f3])).
% 1.52/0.59  fof(f3,axiom,(
% 1.52/0.59    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.52/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.52/0.59  fof(f104,plain,(
% 1.52/0.59    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) | spl5_1),
% 1.52/0.59    inference(avatar_component_clause,[],[f102])).
% 1.52/0.59  fof(f110,plain,(
% 1.52/0.59    spl5_2),
% 1.52/0.59    inference(avatar_split_clause,[],[f65,f107])).
% 1.52/0.59  fof(f65,plain,(
% 1.52/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.52/0.59    inference(cnf_transformation,[],[f51])).
% 1.52/0.59  fof(f105,plain,(
% 1.52/0.59    ~spl5_1),
% 1.52/0.59    inference(avatar_split_clause,[],[f66,f102])).
% 1.52/0.59  fof(f66,plain,(
% 1.52/0.59    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)),
% 1.52/0.59    inference(cnf_transformation,[],[f51])).
% 1.52/0.59  % SZS output end Proof for theBenchmark
% 1.52/0.59  % (29778)------------------------------
% 1.52/0.59  % (29778)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.59  % (29778)Termination reason: Refutation
% 1.52/0.59  
% 1.52/0.59  % (29778)Memory used [KB]: 6780
% 1.52/0.59  % (29778)Time elapsed: 0.150 s
% 1.52/0.59  % (29778)------------------------------
% 1.52/0.59  % (29778)------------------------------
% 1.52/0.59  % (29748)Success in time 0.23 s
%------------------------------------------------------------------------------
