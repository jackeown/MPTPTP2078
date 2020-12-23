%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:43 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 264 expanded)
%              Number of leaves         :   28 (  96 expanded)
%              Depth                    :   14
%              Number of atoms          :  461 (1188 expanded)
%              Number of equality atoms :   78 ( 228 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f599,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f91,f96,f106,f109,f134,f137,f157,f266,f278,f282,f299,f435,f478,f488,f489,f574,f598])).

fof(f598,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | spl4_19
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f575,f571,f296,f93,f88])).

fof(f88,plain,
    ( spl4_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f93,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f296,plain,
    ( spl4_19
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f571,plain,
    ( spl4_27
  <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f575,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_27 ),
    inference(superposition,[],[f573,f215])).

fof(f215,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f214])).

fof(f214,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f50,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f573,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f571])).

fof(f574,plain,
    ( spl4_27
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f569,f131,f571])).

fof(f131,plain,
    ( spl4_7
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f569,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_7 ),
    inference(duplicate_literal_removal,[],[f560])).

fof(f560,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_7 ),
    inference(resolution,[],[f498,f164])).

fof(f164,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f498,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK2(X2,k2_tops_1(sK0,sK1),X2),sK1)
        | k4_xboole_0(X2,k2_tops_1(sK0,sK1)) = X2 )
    | ~ spl4_7 ),
    inference(resolution,[],[f482,f289])).

fof(f289,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK2(X3,X4,X3),X4)
      | k4_xboole_0(X3,X4) = X3 ) ),
    inference(global_subsumption,[],[f164,f287])).

fof(f287,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK2(X3,X4,X3),X4)
      | ~ r2_hidden(sK2(X3,X4,X3),X3)
      | k4_xboole_0(X3,X4) = X3 ) ),
    inference(duplicate_literal_removal,[],[f284])).

fof(f284,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK2(X3,X4,X3),X4)
      | ~ r2_hidden(sK2(X3,X4,X3),X3)
      | k4_xboole_0(X3,X4) = X3
      | k4_xboole_0(X3,X4) = X3 ) ),
    inference(resolution,[],[f61,f164])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f482,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k2_tops_1(sK0,sK1))
        | ~ r2_hidden(X2,sK1) )
    | ~ spl4_7 ),
    inference(superposition,[],[f75,f133])).

fof(f133,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f131])).

fof(f75,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f489,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f488,plain,
    ( spl4_5
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f486])).

fof(f486,plain,
    ( $false
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f128,f485])).

fof(f485,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_5
    | ~ spl4_7 ),
    inference(trivial_inequality_removal,[],[f484])).

fof(f484,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_5
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f229,f133])).

fof(f229,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_5 ),
    inference(superposition,[],[f104,f50])).

fof(f104,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl4_5
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f128,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl4_6
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f478,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | spl4_7
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f455,f296,f131,f93,f88])).

fof(f455,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_19 ),
    inference(superposition,[],[f239,f298])).

fof(f298,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f296])).

fof(f239,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k4_xboole_0(k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(global_subsumption,[],[f53,f238])).

fof(f238,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k4_xboole_0(k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f50,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f435,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | spl4_18 ),
    inference(avatar_contradiction_clause,[],[f430])).

fof(f430,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | spl4_18 ),
    inference(unit_resulting_resolution,[],[f90,f294,f95,f363])).

fof(f363,plain,(
    ! [X12,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X12)))
      | r1_tarski(k1_tops_1(X12,X11),X11)
      | ~ l1_pre_topc(X12) ) ),
    inference(superposition,[],[f62,f215])).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f95,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f294,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | spl4_18 ),
    inference(avatar_component_clause,[],[f292])).

fof(f292,plain,
    ( spl4_18
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f90,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f299,plain,
    ( ~ spl4_18
    | spl4_19
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f290,f271,f296,f292])).

fof(f271,plain,
    ( spl4_16
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f290,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl4_16 ),
    inference(resolution,[],[f273,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f273,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f271])).

fof(f282,plain,(
    spl4_17 ),
    inference(avatar_contradiction_clause,[],[f279])).

fof(f279,plain,
    ( $false
    | spl4_17 ),
    inference(unit_resulting_resolution,[],[f77,f277])).

fof(f277,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl4_17 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl4_17
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f278,plain,
    ( ~ spl4_4
    | spl4_16
    | ~ spl4_17
    | ~ spl4_3
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f267,f264,f93,f275,f271,f99])).

fof(f99,plain,
    ( spl4_4
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f264,plain,
    ( spl4_15
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,k1_tops_1(sK0,sK1))
        | ~ v3_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f267,plain,
    ( ~ r1_tarski(sK1,sK1)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl4_3
    | ~ spl4_15 ),
    inference(resolution,[],[f265,f95])).

fof(f265,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK1)
        | r1_tarski(X0,k1_tops_1(sK0,sK1))
        | ~ v3_pre_topc(X0,sK0) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f264])).

fof(f266,plain,
    ( ~ spl4_2
    | spl4_15
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f259,f93,f264,f88])).

fof(f259,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ v3_pre_topc(X0,sK0)
        | r1_tarski(X0,k1_tops_1(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f55,f95])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(f157,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_9
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f143,f93,f154,f88,f83])).

fof(f83,plain,
    ( spl4_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f154,plain,
    ( spl4_9
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f143,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f54,f95])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f137,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f90,f95,f129,f53])).

fof(f129,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f127])).

fof(f134,plain,
    ( ~ spl4_6
    | spl4_7
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f124,f103,f131,f127])).

fof(f124,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_5 ),
    inference(superposition,[],[f50,f105])).

fof(f105,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f109,plain,
    ( ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f108,f103,f99])).

fof(f108,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl4_5 ),
    inference(trivial_inequality_removal,[],[f107])).

fof(f107,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f49,f105])).

fof(f49,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f106,plain,
    ( spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f48,f103,f99])).

fof(f48,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f96,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f47,f93])).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f91,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f46,f88])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f86,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f45,f83])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:25:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.51  % (32040)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.51  % (32056)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.51  % (32057)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.51  % (32048)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.52  % (32049)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.52  % (32067)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (32067)Refutation not found, incomplete strategy% (32067)------------------------------
% 0.22/0.52  % (32067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (32067)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (32067)Memory used [KB]: 1663
% 0.22/0.53  % (32067)Time elapsed: 0.004 s
% 0.22/0.53  % (32067)------------------------------
% 0.22/0.53  % (32067)------------------------------
% 0.22/0.53  % (32043)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (32048)Refutation not found, incomplete strategy% (32048)------------------------------
% 0.22/0.53  % (32048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (32048)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (32048)Memory used [KB]: 10746
% 0.22/0.53  % (32048)Time elapsed: 0.116 s
% 0.22/0.53  % (32048)------------------------------
% 0.22/0.53  % (32048)------------------------------
% 0.22/0.54  % (32051)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (32041)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (32065)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (32042)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (32039)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (32065)Refutation not found, incomplete strategy% (32065)------------------------------
% 0.22/0.54  % (32065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (32065)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (32065)Memory used [KB]: 6268
% 0.22/0.54  % (32065)Time elapsed: 0.125 s
% 0.22/0.54  % (32065)------------------------------
% 0.22/0.54  % (32065)------------------------------
% 0.22/0.54  % (32059)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (32044)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (32046)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (32058)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (32055)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.48/0.55  % (32052)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.48/0.55  % (32054)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.48/0.55  % (32045)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.48/0.55  % (32038)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.48/0.55  % (32066)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.48/0.55  % (32054)Refutation not found, incomplete strategy% (32054)------------------------------
% 1.48/0.55  % (32054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  % (32054)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.55  
% 1.48/0.55  % (32054)Memory used [KB]: 10746
% 1.48/0.55  % (32054)Time elapsed: 0.135 s
% 1.48/0.55  % (32054)------------------------------
% 1.48/0.55  % (32054)------------------------------
% 1.48/0.55  % (32047)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.48/0.55  % (32066)Refutation not found, incomplete strategy% (32066)------------------------------
% 1.48/0.55  % (32066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  % (32066)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.55  
% 1.48/0.55  % (32066)Memory used [KB]: 10746
% 1.48/0.55  % (32066)Time elapsed: 0.137 s
% 1.48/0.55  % (32066)------------------------------
% 1.48/0.55  % (32066)------------------------------
% 1.48/0.55  % (32064)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.48/0.56  % (32062)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.48/0.56  % (32060)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.48/0.56  % (32050)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.48/0.56  % (32063)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.48/0.56  % (32061)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.57/0.57  % (32053)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.57/0.60  % (32061)Refutation found. Thanks to Tanya!
% 1.57/0.60  % SZS status Theorem for theBenchmark
% 1.57/0.62  % SZS output start Proof for theBenchmark
% 1.57/0.62  fof(f599,plain,(
% 1.57/0.62    $false),
% 1.57/0.62    inference(avatar_sat_refutation,[],[f86,f91,f96,f106,f109,f134,f137,f157,f266,f278,f282,f299,f435,f478,f488,f489,f574,f598])).
% 1.57/0.62  fof(f598,plain,(
% 1.57/0.62    ~spl4_2 | ~spl4_3 | spl4_19 | ~spl4_27),
% 1.57/0.62    inference(avatar_split_clause,[],[f575,f571,f296,f93,f88])).
% 1.57/0.62  fof(f88,plain,(
% 1.57/0.62    spl4_2 <=> l1_pre_topc(sK0)),
% 1.57/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.57/0.62  fof(f93,plain,(
% 1.57/0.62    spl4_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.57/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.57/0.62  fof(f296,plain,(
% 1.57/0.62    spl4_19 <=> sK1 = k1_tops_1(sK0,sK1)),
% 1.57/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.57/0.62  fof(f571,plain,(
% 1.57/0.62    spl4_27 <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 1.57/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 1.57/0.62  fof(f575,plain,(
% 1.57/0.62    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_27),
% 1.57/0.62    inference(superposition,[],[f573,f215])).
% 1.57/0.62  fof(f215,plain,(
% 1.57/0.62    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.57/0.62    inference(duplicate_literal_removal,[],[f214])).
% 1.57/0.62  fof(f214,plain,(
% 1.57/0.62    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.57/0.62    inference(superposition,[],[f50,f52])).
% 1.57/0.62  fof(f52,plain,(
% 1.57/0.62    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.57/0.62    inference(cnf_transformation,[],[f21])).
% 1.57/0.62  fof(f21,plain,(
% 1.57/0.62    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.57/0.62    inference(ennf_transformation,[],[f14])).
% 1.57/0.62  fof(f14,axiom,(
% 1.57/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.57/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 1.57/0.62  fof(f50,plain,(
% 1.57/0.62    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.57/0.62    inference(cnf_transformation,[],[f19])).
% 1.57/0.62  fof(f19,plain,(
% 1.57/0.62    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.57/0.62    inference(ennf_transformation,[],[f8])).
% 1.57/0.62  fof(f8,axiom,(
% 1.57/0.62    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.57/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.57/0.62  fof(f573,plain,(
% 1.57/0.62    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl4_27),
% 1.57/0.62    inference(avatar_component_clause,[],[f571])).
% 1.57/0.62  fof(f574,plain,(
% 1.57/0.62    spl4_27 | ~spl4_7),
% 1.57/0.62    inference(avatar_split_clause,[],[f569,f131,f571])).
% 1.57/0.62  fof(f131,plain,(
% 1.57/0.62    spl4_7 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 1.57/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.57/0.62  fof(f569,plain,(
% 1.57/0.62    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl4_7),
% 1.57/0.62    inference(duplicate_literal_removal,[],[f560])).
% 1.57/0.62  fof(f560,plain,(
% 1.57/0.62    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl4_7),
% 1.57/0.62    inference(resolution,[],[f498,f164])).
% 1.57/0.62  fof(f164,plain,(
% 1.57/0.62    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) )),
% 1.57/0.62    inference(factoring,[],[f59])).
% 1.57/0.62  fof(f59,plain,(
% 1.57/0.62    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 1.57/0.62    inference(cnf_transformation,[],[f37])).
% 1.57/0.62  fof(f37,plain,(
% 1.57/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.57/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).
% 1.57/0.62  fof(f36,plain,(
% 1.57/0.62    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.57/0.62    introduced(choice_axiom,[])).
% 1.57/0.62  fof(f35,plain,(
% 1.57/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.57/0.62    inference(rectify,[],[f34])).
% 1.57/0.62  fof(f34,plain,(
% 1.57/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.57/0.62    inference(flattening,[],[f33])).
% 1.57/0.62  fof(f33,plain,(
% 1.57/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.57/0.62    inference(nnf_transformation,[],[f2])).
% 1.57/0.62  fof(f2,axiom,(
% 1.57/0.62    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.57/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.57/0.62  fof(f498,plain,(
% 1.57/0.62    ( ! [X2] : (~r2_hidden(sK2(X2,k2_tops_1(sK0,sK1),X2),sK1) | k4_xboole_0(X2,k2_tops_1(sK0,sK1)) = X2) ) | ~spl4_7),
% 1.57/0.62    inference(resolution,[],[f482,f289])).
% 1.57/0.62  fof(f289,plain,(
% 1.57/0.62    ( ! [X4,X3] : (r2_hidden(sK2(X3,X4,X3),X4) | k4_xboole_0(X3,X4) = X3) )),
% 1.57/0.62    inference(global_subsumption,[],[f164,f287])).
% 1.57/0.62  fof(f287,plain,(
% 1.57/0.62    ( ! [X4,X3] : (r2_hidden(sK2(X3,X4,X3),X4) | ~r2_hidden(sK2(X3,X4,X3),X3) | k4_xboole_0(X3,X4) = X3) )),
% 1.57/0.62    inference(duplicate_literal_removal,[],[f284])).
% 1.57/0.62  fof(f284,plain,(
% 1.57/0.62    ( ! [X4,X3] : (r2_hidden(sK2(X3,X4,X3),X4) | ~r2_hidden(sK2(X3,X4,X3),X3) | k4_xboole_0(X3,X4) = X3 | k4_xboole_0(X3,X4) = X3) )),
% 1.57/0.62    inference(resolution,[],[f61,f164])).
% 1.57/0.62  fof(f61,plain,(
% 1.57/0.62    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 1.57/0.62    inference(cnf_transformation,[],[f37])).
% 1.57/0.62  fof(f482,plain,(
% 1.57/0.62    ( ! [X2] : (~r2_hidden(X2,k2_tops_1(sK0,sK1)) | ~r2_hidden(X2,sK1)) ) | ~spl4_7),
% 1.57/0.62    inference(superposition,[],[f75,f133])).
% 1.57/0.62  fof(f133,plain,(
% 1.57/0.62    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl4_7),
% 1.57/0.62    inference(avatar_component_clause,[],[f131])).
% 1.57/0.62  fof(f75,plain,(
% 1.57/0.62    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.57/0.62    inference(equality_resolution,[],[f57])).
% 1.57/0.62  fof(f57,plain,(
% 1.57/0.62    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.57/0.62    inference(cnf_transformation,[],[f37])).
% 1.57/0.62  fof(f489,plain,(
% 1.57/0.62    sK1 != k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 1.57/0.62    introduced(theory_tautology_sat_conflict,[])).
% 1.57/0.62  fof(f488,plain,(
% 1.57/0.62    spl4_5 | ~spl4_6 | ~spl4_7),
% 1.57/0.62    inference(avatar_contradiction_clause,[],[f486])).
% 1.57/0.62  fof(f486,plain,(
% 1.57/0.62    $false | (spl4_5 | ~spl4_6 | ~spl4_7)),
% 1.57/0.62    inference(subsumption_resolution,[],[f128,f485])).
% 1.57/0.62  fof(f485,plain,(
% 1.57/0.62    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_5 | ~spl4_7)),
% 1.57/0.62    inference(trivial_inequality_removal,[],[f484])).
% 1.57/0.62  fof(f484,plain,(
% 1.57/0.62    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_5 | ~spl4_7)),
% 1.57/0.62    inference(forward_demodulation,[],[f229,f133])).
% 1.57/0.62  fof(f229,plain,(
% 1.57/0.62    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_5),
% 1.57/0.62    inference(superposition,[],[f104,f50])).
% 1.57/0.62  fof(f104,plain,(
% 1.57/0.62    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl4_5),
% 1.57/0.62    inference(avatar_component_clause,[],[f103])).
% 1.57/0.62  fof(f103,plain,(
% 1.57/0.62    spl4_5 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 1.57/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.57/0.62  fof(f128,plain,(
% 1.57/0.62    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_6),
% 1.57/0.62    inference(avatar_component_clause,[],[f127])).
% 1.57/0.62  fof(f127,plain,(
% 1.57/0.62    spl4_6 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.57/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.57/0.62  fof(f478,plain,(
% 1.57/0.62    ~spl4_2 | ~spl4_3 | spl4_7 | ~spl4_19),
% 1.57/0.62    inference(avatar_split_clause,[],[f455,f296,f131,f93,f88])).
% 1.57/0.62  fof(f455,plain,(
% 1.57/0.62    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_19),
% 1.57/0.62    inference(superposition,[],[f239,f298])).
% 1.57/0.62  fof(f298,plain,(
% 1.57/0.62    sK1 = k1_tops_1(sK0,sK1) | ~spl4_19),
% 1.57/0.62    inference(avatar_component_clause,[],[f296])).
% 1.57/0.62  fof(f239,plain,(
% 1.57/0.62    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k4_xboole_0(k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.57/0.62    inference(global_subsumption,[],[f53,f238])).
% 1.57/0.62  fof(f238,plain,(
% 1.57/0.62    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k4_xboole_0(k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.57/0.62    inference(superposition,[],[f50,f51])).
% 1.57/0.62  fof(f51,plain,(
% 1.57/0.62    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.57/0.62    inference(cnf_transformation,[],[f20])).
% 1.57/0.62  fof(f20,plain,(
% 1.57/0.62    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.57/0.62    inference(ennf_transformation,[],[f12])).
% 1.57/0.62  fof(f12,axiom,(
% 1.57/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 1.57/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 1.57/0.62  fof(f53,plain,(
% 1.57/0.62    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.57/0.62    inference(cnf_transformation,[],[f23])).
% 1.57/0.62  fof(f23,plain,(
% 1.57/0.62    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.57/0.62    inference(flattening,[],[f22])).
% 1.57/0.62  fof(f22,plain,(
% 1.57/0.62    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.57/0.62    inference(ennf_transformation,[],[f10])).
% 1.57/0.62  fof(f10,axiom,(
% 1.57/0.62    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.57/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 1.57/0.62  fof(f435,plain,(
% 1.57/0.62    ~spl4_2 | ~spl4_3 | spl4_18),
% 1.57/0.62    inference(avatar_contradiction_clause,[],[f430])).
% 1.57/0.62  fof(f430,plain,(
% 1.57/0.62    $false | (~spl4_2 | ~spl4_3 | spl4_18)),
% 1.57/0.62    inference(unit_resulting_resolution,[],[f90,f294,f95,f363])).
% 1.57/0.62  fof(f363,plain,(
% 1.57/0.62    ( ! [X12,X11] : (~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X12))) | r1_tarski(k1_tops_1(X12,X11),X11) | ~l1_pre_topc(X12)) )),
% 1.57/0.62    inference(superposition,[],[f62,f215])).
% 1.57/0.62  fof(f62,plain,(
% 1.57/0.62    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.57/0.62    inference(cnf_transformation,[],[f6])).
% 1.57/0.62  fof(f6,axiom,(
% 1.57/0.62    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.57/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.57/0.62  fof(f95,plain,(
% 1.57/0.62    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_3),
% 1.57/0.62    inference(avatar_component_clause,[],[f93])).
% 1.57/0.62  fof(f294,plain,(
% 1.57/0.62    ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | spl4_18),
% 1.57/0.62    inference(avatar_component_clause,[],[f292])).
% 1.57/0.62  fof(f292,plain,(
% 1.57/0.62    spl4_18 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.57/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.57/0.62  fof(f90,plain,(
% 1.57/0.62    l1_pre_topc(sK0) | ~spl4_2),
% 1.57/0.62    inference(avatar_component_clause,[],[f88])).
% 1.57/0.62  fof(f299,plain,(
% 1.57/0.62    ~spl4_18 | spl4_19 | ~spl4_16),
% 1.57/0.62    inference(avatar_split_clause,[],[f290,f271,f296,f292])).
% 1.57/0.62  fof(f271,plain,(
% 1.57/0.62    spl4_16 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 1.57/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.57/0.62  fof(f290,plain,(
% 1.57/0.62    sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl4_16),
% 1.57/0.62    inference(resolution,[],[f273,f66])).
% 1.57/0.62  fof(f66,plain,(
% 1.57/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.57/0.62    inference(cnf_transformation,[],[f39])).
% 1.57/0.62  fof(f39,plain,(
% 1.57/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.57/0.62    inference(flattening,[],[f38])).
% 1.57/0.62  fof(f38,plain,(
% 1.57/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.57/0.62    inference(nnf_transformation,[],[f3])).
% 1.57/0.62  fof(f3,axiom,(
% 1.57/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.57/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.57/0.62  fof(f273,plain,(
% 1.57/0.62    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~spl4_16),
% 1.57/0.62    inference(avatar_component_clause,[],[f271])).
% 1.57/0.62  fof(f282,plain,(
% 1.57/0.62    spl4_17),
% 1.57/0.62    inference(avatar_contradiction_clause,[],[f279])).
% 1.57/0.62  fof(f279,plain,(
% 1.57/0.62    $false | spl4_17),
% 1.57/0.62    inference(unit_resulting_resolution,[],[f77,f277])).
% 1.57/0.62  fof(f277,plain,(
% 1.57/0.62    ~r1_tarski(sK1,sK1) | spl4_17),
% 1.57/0.62    inference(avatar_component_clause,[],[f275])).
% 1.57/0.62  fof(f275,plain,(
% 1.57/0.62    spl4_17 <=> r1_tarski(sK1,sK1)),
% 1.57/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.57/0.62  fof(f77,plain,(
% 1.57/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.57/0.62    inference(equality_resolution,[],[f65])).
% 1.57/0.62  fof(f65,plain,(
% 1.57/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.57/0.62    inference(cnf_transformation,[],[f39])).
% 1.57/0.62  fof(f278,plain,(
% 1.57/0.62    ~spl4_4 | spl4_16 | ~spl4_17 | ~spl4_3 | ~spl4_15),
% 1.57/0.62    inference(avatar_split_clause,[],[f267,f264,f93,f275,f271,f99])).
% 1.57/0.62  fof(f99,plain,(
% 1.57/0.62    spl4_4 <=> v3_pre_topc(sK1,sK0)),
% 1.57/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.57/0.62  fof(f264,plain,(
% 1.57/0.62    spl4_15 <=> ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~v3_pre_topc(X0,sK0))),
% 1.57/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.57/0.62  fof(f267,plain,(
% 1.57/0.62    ~r1_tarski(sK1,sK1) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0) | (~spl4_3 | ~spl4_15)),
% 1.57/0.62    inference(resolution,[],[f265,f95])).
% 1.57/0.62  fof(f265,plain,(
% 1.57/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~v3_pre_topc(X0,sK0)) ) | ~spl4_15),
% 1.57/0.62    inference(avatar_component_clause,[],[f264])).
% 1.57/0.62  fof(f266,plain,(
% 1.57/0.62    ~spl4_2 | spl4_15 | ~spl4_3),
% 1.57/0.62    inference(avatar_split_clause,[],[f259,f93,f264,f88])).
% 1.57/0.62  fof(f259,plain,(
% 1.57/0.62    ( ! [X0] : (~r1_tarski(X0,sK1) | ~v3_pre_topc(X0,sK0) | r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl4_3),
% 1.57/0.62    inference(resolution,[],[f55,f95])).
% 1.57/0.62  fof(f55,plain,(
% 1.57/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.57/0.62    inference(cnf_transformation,[],[f27])).
% 1.57/0.62  fof(f27,plain,(
% 1.57/0.62    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.57/0.62    inference(flattening,[],[f26])).
% 1.57/0.62  fof(f26,plain,(
% 1.57/0.62    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.57/0.62    inference(ennf_transformation,[],[f13])).
% 1.57/0.62  fof(f13,axiom,(
% 1.57/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 1.57/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 1.57/0.62  fof(f157,plain,(
% 1.57/0.62    ~spl4_1 | ~spl4_2 | spl4_9 | ~spl4_3),
% 1.57/0.62    inference(avatar_split_clause,[],[f143,f93,f154,f88,f83])).
% 1.57/0.62  fof(f83,plain,(
% 1.57/0.62    spl4_1 <=> v2_pre_topc(sK0)),
% 1.57/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.57/0.62  fof(f154,plain,(
% 1.57/0.62    spl4_9 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 1.57/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.57/0.62  fof(f143,plain,(
% 1.57/0.62    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl4_3),
% 1.57/0.62    inference(resolution,[],[f54,f95])).
% 1.57/0.62  fof(f54,plain,(
% 1.57/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.57/0.62    inference(cnf_transformation,[],[f25])).
% 1.57/0.62  fof(f25,plain,(
% 1.57/0.62    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.57/0.62    inference(flattening,[],[f24])).
% 1.57/0.62  fof(f24,plain,(
% 1.57/0.62    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.57/0.62    inference(ennf_transformation,[],[f11])).
% 1.57/0.62  fof(f11,axiom,(
% 1.57/0.62    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.57/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 1.57/0.62  fof(f137,plain,(
% 1.57/0.62    ~spl4_2 | ~spl4_3 | spl4_6),
% 1.57/0.62    inference(avatar_contradiction_clause,[],[f135])).
% 1.57/0.62  fof(f135,plain,(
% 1.57/0.62    $false | (~spl4_2 | ~spl4_3 | spl4_6)),
% 1.57/0.62    inference(unit_resulting_resolution,[],[f90,f95,f129,f53])).
% 1.57/0.62  fof(f129,plain,(
% 1.57/0.62    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_6),
% 1.57/0.62    inference(avatar_component_clause,[],[f127])).
% 1.57/0.62  fof(f134,plain,(
% 1.57/0.62    ~spl4_6 | spl4_7 | ~spl4_5),
% 1.57/0.62    inference(avatar_split_clause,[],[f124,f103,f131,f127])).
% 1.57/0.62  fof(f124,plain,(
% 1.57/0.62    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_5),
% 1.57/0.62    inference(superposition,[],[f50,f105])).
% 1.57/0.62  fof(f105,plain,(
% 1.57/0.62    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl4_5),
% 1.57/0.62    inference(avatar_component_clause,[],[f103])).
% 1.57/0.62  fof(f109,plain,(
% 1.57/0.62    ~spl4_4 | ~spl4_5),
% 1.57/0.62    inference(avatar_split_clause,[],[f108,f103,f99])).
% 1.57/0.62  fof(f108,plain,(
% 1.57/0.62    ~v3_pre_topc(sK1,sK0) | ~spl4_5),
% 1.57/0.62    inference(trivial_inequality_removal,[],[f107])).
% 1.57/0.62  fof(f107,plain,(
% 1.57/0.62    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | ~spl4_5),
% 1.57/0.62    inference(forward_demodulation,[],[f49,f105])).
% 1.57/0.62  fof(f49,plain,(
% 1.57/0.62    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 1.57/0.62    inference(cnf_transformation,[],[f32])).
% 1.57/0.62  fof(f32,plain,(
% 1.57/0.62    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.57/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f31,f30])).
% 1.57/0.62  fof(f30,plain,(
% 1.57/0.62    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.57/0.62    introduced(choice_axiom,[])).
% 1.57/0.62  fof(f31,plain,(
% 1.57/0.62    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.57/0.62    introduced(choice_axiom,[])).
% 1.57/0.62  fof(f29,plain,(
% 1.57/0.62    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.57/0.62    inference(flattening,[],[f28])).
% 1.57/0.62  fof(f28,plain,(
% 1.57/0.62    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.57/0.62    inference(nnf_transformation,[],[f18])).
% 1.57/0.62  fof(f18,plain,(
% 1.57/0.62    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.57/0.62    inference(flattening,[],[f17])).
% 1.57/0.62  fof(f17,plain,(
% 1.57/0.62    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.57/0.62    inference(ennf_transformation,[],[f16])).
% 1.57/0.62  fof(f16,negated_conjecture,(
% 1.57/0.62    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 1.57/0.62    inference(negated_conjecture,[],[f15])).
% 1.57/0.62  fof(f15,conjecture,(
% 1.57/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 1.57/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 1.57/0.62  fof(f106,plain,(
% 1.57/0.62    spl4_4 | spl4_5),
% 1.57/0.62    inference(avatar_split_clause,[],[f48,f103,f99])).
% 1.57/0.62  fof(f48,plain,(
% 1.57/0.62    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 1.57/0.62    inference(cnf_transformation,[],[f32])).
% 1.57/0.62  fof(f96,plain,(
% 1.57/0.62    spl4_3),
% 1.57/0.62    inference(avatar_split_clause,[],[f47,f93])).
% 1.57/0.62  fof(f47,plain,(
% 1.57/0.62    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.57/0.62    inference(cnf_transformation,[],[f32])).
% 1.57/0.62  fof(f91,plain,(
% 1.57/0.62    spl4_2),
% 1.57/0.62    inference(avatar_split_clause,[],[f46,f88])).
% 1.57/0.62  fof(f46,plain,(
% 1.57/0.62    l1_pre_topc(sK0)),
% 1.57/0.62    inference(cnf_transformation,[],[f32])).
% 1.57/0.62  fof(f86,plain,(
% 1.57/0.62    spl4_1),
% 1.57/0.62    inference(avatar_split_clause,[],[f45,f83])).
% 1.57/0.62  fof(f45,plain,(
% 1.57/0.62    v2_pre_topc(sK0)),
% 1.57/0.62    inference(cnf_transformation,[],[f32])).
% 1.57/0.62  % SZS output end Proof for theBenchmark
% 1.57/0.62  % (32061)------------------------------
% 1.57/0.62  % (32061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.62  % (32061)Termination reason: Refutation
% 1.57/0.62  
% 1.57/0.62  % (32061)Memory used [KB]: 11129
% 1.57/0.62  % (32061)Time elapsed: 0.192 s
% 1.57/0.62  % (32061)------------------------------
% 1.57/0.62  % (32061)------------------------------
% 1.57/0.62  % (32037)Success in time 0.257 s
%------------------------------------------------------------------------------
