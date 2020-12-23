%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0423+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:57 EST 2020

% Result     : Theorem 40.06s
% Output     : Refutation 40.06s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 303 expanded)
%              Number of leaves         :   41 ( 129 expanded)
%              Depth                    :    8
%              Number of atoms          :  419 ( 742 expanded)
%              Number of equality atoms :   92 ( 166 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f28484,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f73,f78,f85,f232,f492,f10141,f10158,f10165,f12036,f12064,f15856,f16402,f16522,f21152,f21582,f21602,f21647,f22422,f22471,f22485,f22551,f23204,f28483])).

fof(f28483,plain,
    ( spl4_869
    | ~ spl4_1128
    | ~ spl4_3
    | spl4_1449 ),
    inference(avatar_split_clause,[],[f28479,f22024,f75,f16373,f12057])).

fof(f12057,plain,
    ( spl4_869
  <=> sK1 = k7_setfam_1(sK0,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_869])])).

fof(f16373,plain,
    ( spl4_1128
  <=> m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1128])])).

fof(f75,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f22024,plain,
    ( spl4_1449
  <=> m1_subset_1(sK2(sK0,k1_tarski(k1_xboole_0),sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1449])])).

fof(f28479,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | sK1 = k7_setfam_1(sK0,k1_tarski(k1_xboole_0))
    | spl4_1449 ),
    inference(resolution,[],[f22026,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

fof(f22026,plain,
    ( ~ m1_subset_1(sK2(sK0,k1_tarski(k1_xboole_0),sK1),k1_zfmisc_1(sK0))
    | spl4_1449 ),
    inference(avatar_component_clause,[],[f22024])).

fof(f23204,plain,
    ( spl4_1403
    | spl4_869
    | ~ spl4_3
    | ~ spl4_1128
    | spl4_870 ),
    inference(avatar_split_clause,[],[f21727,f12061,f16373,f75,f12057,f21494])).

fof(f21494,plain,
    ( spl4_1403
  <=> k1_xboole_0 = k3_subset_1(sK0,sK2(sK0,k1_tarski(k1_xboole_0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1403])])).

fof(f12061,plain,
    ( spl4_870
  <=> r2_hidden(sK2(sK0,k1_tarski(k1_xboole_0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_870])])).

fof(f21727,plain,
    ( ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | sK1 = k7_setfam_1(sK0,k1_tarski(k1_xboole_0))
    | k1_xboole_0 = k3_subset_1(sK0,sK2(sK0,k1_tarski(k1_xboole_0),sK1))
    | spl4_870 ),
    inference(resolution,[],[f12063,f511])).

fof(f511,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X1,k1_tarski(X2),X0),X0)
      | ~ m1_subset_1(k1_tarski(X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | k7_setfam_1(X1,k1_tarski(X2)) = X0
      | k3_subset_1(X1,sK2(X1,k1_tarski(X2),X0)) = X2 ) ),
    inference(resolution,[],[f42,f61])).

fof(f61,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k7_setfam_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12063,plain,
    ( ~ r2_hidden(sK2(sK0,k1_tarski(k1_xboole_0),sK1),sK1)
    | spl4_870 ),
    inference(avatar_component_clause,[],[f12061])).

fof(f22551,plain,
    ( sK1 != k7_setfam_1(sK0,k1_tarski(k1_xboole_0))
    | k1_tarski(k1_xboole_0) != k7_setfam_1(sK0,k7_setfam_1(sK0,k1_tarski(k1_xboole_0)))
    | k1_tarski(k1_xboole_0) = k7_setfam_1(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f22485,plain,
    ( ~ spl4_3
    | ~ spl4_723
    | ~ spl4_39
    | ~ spl4_4
    | spl4_1481 ),
    inference(avatar_split_clause,[],[f22484,f22468,f82,f454,f9952,f75])).

fof(f9952,plain,
    ( spl4_723
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_723])])).

fof(f454,plain,
    ( spl4_39
  <=> m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f82,plain,
    ( spl4_4
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f22468,plain,
    ( spl4_1481
  <=> r2_hidden(k1_xboole_0,k7_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1481])])).

fof(f22484,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl4_1481 ),
    inference(forward_demodulation,[],[f22482,f1186])).

fof(f1186,plain,(
    ! [X6] : k3_subset_1(X6,k1_xboole_0) = X6 ),
    inference(forward_demodulation,[],[f1180,f36])).

fof(f36,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f1180,plain,(
    ! [X6] : k3_subset_1(X6,k1_xboole_0) = k4_xboole_0(X6,k1_xboole_0) ),
    inference(resolution,[],[f194,f34])).

fof(f34,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f194,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,X1)
      | k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(resolution,[],[f39,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f22482,plain,
    ( ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ r2_hidden(k3_subset_1(sK0,k1_xboole_0),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl4_1481 ),
    inference(resolution,[],[f22470,f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ r2_hidden(k3_subset_1(X0,X3),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ r2_hidden(k3_subset_1(X0,X3),X1)
      | r2_hidden(X3,X2)
      | k7_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f22470,plain,
    ( ~ r2_hidden(k1_xboole_0,k7_setfam_1(sK0,sK1))
    | spl4_1481 ),
    inference(avatar_component_clause,[],[f22468])).

fof(f22471,plain,
    ( spl4_870
    | ~ spl4_1481
    | ~ spl4_40
    | ~ spl4_1403
    | ~ spl4_1449 ),
    inference(avatar_split_clause,[],[f22466,f22024,f21494,f458,f22468,f12061])).

fof(f458,plain,
    ( spl4_40
  <=> ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(k3_subset_1(sK0,X0),k7_setfam_1(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f22466,plain,
    ( ~ r2_hidden(k1_xboole_0,k7_setfam_1(sK0,sK1))
    | r2_hidden(sK2(sK0,k1_tarski(k1_xboole_0),sK1),sK1)
    | ~ spl4_40
    | ~ spl4_1403
    | ~ spl4_1449 ),
    inference(forward_demodulation,[],[f22450,f21496])).

fof(f21496,plain,
    ( k1_xboole_0 = k3_subset_1(sK0,sK2(sK0,k1_tarski(k1_xboole_0),sK1))
    | ~ spl4_1403 ),
    inference(avatar_component_clause,[],[f21494])).

fof(f22450,plain,
    ( ~ r2_hidden(k3_subset_1(sK0,sK2(sK0,k1_tarski(k1_xboole_0),sK1)),k7_setfam_1(sK0,sK1))
    | r2_hidden(sK2(sK0,k1_tarski(k1_xboole_0),sK1),sK1)
    | ~ spl4_40
    | ~ spl4_1449 ),
    inference(resolution,[],[f459,f22025])).

fof(f22025,plain,
    ( m1_subset_1(sK2(sK0,k1_tarski(k1_xboole_0),sK1),k1_zfmisc_1(sK0))
    | ~ spl4_1449 ),
    inference(avatar_component_clause,[],[f22024])).

fof(f459,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ r2_hidden(k3_subset_1(sK0,X0),k7_setfam_1(sK0,sK1))
        | r2_hidden(X0,sK1) )
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f458])).

fof(f22422,plain,
    ( ~ spl4_39
    | ~ spl4_3
    | spl4_40
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f11233,f229,f458,f75,f454])).

fof(f229,plain,
    ( spl4_19
  <=> sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f11233,plain,
    ( ! [X1] :
        ( r2_hidden(X1,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
        | ~ r2_hidden(k3_subset_1(sK0,X1),k7_setfam_1(sK0,sK1))
        | ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) )
    | ~ spl4_19 ),
    inference(superposition,[],[f60,f231])).

fof(f231,plain,
    ( sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f229])).

fof(f21647,plain,
    ( sK0 != sK2(sK0,k1_tarski(k1_xboole_0),sK1)
    | k3_subset_1(sK0,sK2(sK0,k1_tarski(k1_xboole_0),sK1)) != k4_xboole_0(sK0,sK2(sK0,k1_tarski(k1_xboole_0),sK1))
    | k1_xboole_0 != k4_xboole_0(sK2(sK0,k1_tarski(k1_xboole_0),sK1),sK0)
    | k1_tarski(k1_xboole_0) != k7_setfam_1(sK0,k7_setfam_1(sK0,k1_tarski(k1_xboole_0)))
    | ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | r2_hidden(k3_subset_1(sK0,sK2(sK0,k1_tarski(k1_xboole_0),sK1)),k1_tarski(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f21602,plain,
    ( spl4_1408
    | ~ spl4_3
    | ~ spl4_870 ),
    inference(avatar_split_clause,[],[f21566,f12061,f75,f21599])).

fof(f21599,plain,
    ( spl4_1408
  <=> k1_xboole_0 = k4_xboole_0(sK2(sK0,k1_tarski(k1_xboole_0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1408])])).

fof(f21566,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2(sK0,k1_tarski(k1_xboole_0),sK1),sK0)
    | ~ spl4_3
    | ~ spl4_870 ),
    inference(resolution,[],[f12062,f3710])).

fof(f3710,plain,
    ( ! [X8] :
        ( ~ r2_hidden(X8,sK1)
        | k1_xboole_0 = k4_xboole_0(X8,sK0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f791,f77])).

fof(f77,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f791,plain,(
    ! [X10,X8,X9] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9)))
      | k1_xboole_0 = k4_xboole_0(X8,X9)
      | ~ r2_hidden(X8,X10) ) ),
    inference(resolution,[],[f113,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f55,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f12062,plain,
    ( r2_hidden(sK2(sK0,k1_tarski(k1_xboole_0),sK1),sK1)
    | ~ spl4_870 ),
    inference(avatar_component_clause,[],[f12061])).

fof(f21582,plain,
    ( spl4_1404
    | ~ spl4_2
    | ~ spl4_870 ),
    inference(avatar_split_clause,[],[f21561,f12061,f70,f21579])).

fof(f21579,plain,
    ( spl4_1404
  <=> sK0 = sK2(sK0,k1_tarski(k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1404])])).

fof(f70,plain,
    ( spl4_2
  <=> sK1 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f21561,plain,
    ( sK0 = sK2(sK0,k1_tarski(k1_xboole_0),sK1)
    | ~ spl4_2
    | ~ spl4_870 ),
    inference(resolution,[],[f12062,f101])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | sK0 = X0 )
    | ~ spl4_2 ),
    inference(superposition,[],[f61,f72])).

fof(f72,plain,
    ( sK1 = k1_tarski(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f21152,plain,
    ( spl4_724
    | ~ spl4_726 ),
    inference(avatar_split_clause,[],[f10160,f10056,f9961])).

fof(f9961,plain,
    ( spl4_724
  <=> k1_tarski(k1_xboole_0) = k7_setfam_1(sK0,k7_setfam_1(sK0,k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_724])])).

fof(f10056,plain,
    ( spl4_726
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_726])])).

fof(f10160,plain,
    ( k1_tarski(k1_xboole_0) = k7_setfam_1(sK0,k7_setfam_1(sK0,k1_tarski(k1_xboole_0)))
    | ~ spl4_726 ),
    inference(resolution,[],[f10057,f1228])).

fof(f1228,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k1_zfmisc_1(X3))
      | k1_tarski(X4) = k7_setfam_1(X3,k7_setfam_1(X3,k1_tarski(X4))) ) ),
    inference(resolution,[],[f226,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f226,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,k1_zfmisc_1(X1))
      | k7_setfam_1(X1,k7_setfam_1(X1,X2)) = X2 ) ),
    inference(resolution,[],[f40,f53])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f10057,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl4_726 ),
    inference(avatar_component_clause,[],[f10056])).

fof(f16522,plain,
    ( spl4_1139
    | spl4_869
    | ~ spl4_3
    | ~ spl4_1128 ),
    inference(avatar_split_clause,[],[f16417,f16373,f75,f12057,f16519])).

fof(f16519,plain,
    ( spl4_1139
  <=> k3_subset_1(sK0,sK2(sK0,k1_tarski(k1_xboole_0),sK1)) = k4_xboole_0(sK0,sK2(sK0,k1_tarski(k1_xboole_0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1139])])).

fof(f16417,plain,
    ( sK1 = k7_setfam_1(sK0,k1_tarski(k1_xboole_0))
    | k3_subset_1(sK0,sK2(sK0,k1_tarski(k1_xboole_0),sK1)) = k4_xboole_0(sK0,sK2(sK0,k1_tarski(k1_xboole_0),sK1))
    | ~ spl4_3
    | ~ spl4_1128 ),
    inference(resolution,[],[f16374,f1605])).

fof(f1605,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | sK1 = k7_setfam_1(sK0,X8)
        | k3_subset_1(sK0,sK2(sK0,X8,sK1)) = k4_xboole_0(sK0,sK2(sK0,X8,sK1)) )
    | ~ spl4_3 ),
    inference(resolution,[],[f367,f77])).

fof(f367,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | k7_setfam_1(X1,X2) = X0
      | k3_subset_1(X1,sK2(X1,X2,X0)) = k4_xboole_0(X1,sK2(X1,X2,X0)) ) ),
    inference(resolution,[],[f46,f39])).

fof(f16374,plain,
    ( m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_1128 ),
    inference(avatar_component_clause,[],[f16373])).

fof(f16402,plain,
    ( ~ spl4_867
    | spl4_1128 ),
    inference(avatar_split_clause,[],[f16399,f16373,f12033])).

fof(f12033,plain,
    ( spl4_867
  <=> r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_867])])).

fof(f16399,plain,
    ( ~ r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(sK0))
    | spl4_1128 ),
    inference(resolution,[],[f16375,f53])).

fof(f16375,plain,
    ( ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl4_1128 ),
    inference(avatar_component_clause,[],[f16373])).

fof(f15856,plain,(
    spl4_958 ),
    inference(avatar_contradiction_clause,[],[f15849])).

fof(f15849,plain,
    ( $false
    | spl4_958 ),
    inference(unit_resulting_resolution,[],[f793,f13209,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f13209,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | spl4_958 ),
    inference(avatar_component_clause,[],[f13207])).

fof(f13207,plain,
    ( spl4_958
  <=> r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_958])])).

fof(f793,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(subsumption_resolution,[],[f689,f792])).

fof(f792,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f193,f785])).

fof(f785,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f113,f79])).

fof(f79,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f37,f35])).

fof(f35,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f37,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f193,plain,(
    ! [X0] : k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f39,f79])).

fof(f689,plain,(
    ! [X0] :
      ( k1_xboole_0 != k3_subset_1(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(superposition,[],[f56,f193])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f12064,plain,
    ( ~ spl4_868
    | spl4_869
    | ~ spl4_870
    | ~ spl4_3
    | ~ spl4_867 ),
    inference(avatar_split_clause,[],[f12038,f12033,f75,f12061,f12057,f12053])).

fof(f12053,plain,
    ( spl4_868
  <=> r2_hidden(k3_subset_1(sK0,sK2(sK0,k1_tarski(k1_xboole_0),sK1)),k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_868])])).

fof(f12038,plain,
    ( ~ r2_hidden(sK2(sK0,k1_tarski(k1_xboole_0),sK1),sK1)
    | sK1 = k7_setfam_1(sK0,k1_tarski(k1_xboole_0))
    | ~ r2_hidden(k3_subset_1(sK0,sK2(sK0,k1_tarski(k1_xboole_0),sK1)),k1_tarski(k1_xboole_0))
    | ~ spl4_3
    | ~ spl4_867 ),
    inference(resolution,[],[f12035,f965])).

fof(f965,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_zfmisc_1(sK0))
        | ~ r2_hidden(sK2(sK0,X0,sK1),sK1)
        | sK1 = k7_setfam_1(sK0,X0)
        | ~ r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,sK1)),X0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f563,f53])).

fof(f563,plain,
    ( ! [X9] :
        ( ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | ~ r2_hidden(k3_subset_1(sK0,sK2(sK0,X9,sK1)),X9)
        | ~ r2_hidden(sK2(sK0,X9,sK1),sK1)
        | sK1 = k7_setfam_1(sK0,X9) )
    | ~ spl4_3 ),
    inference(resolution,[],[f43,f77])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | k7_setfam_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12035,plain,
    ( r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(sK0))
    | ~ spl4_867 ),
    inference(avatar_component_clause,[],[f12033])).

fof(f12036,plain,
    ( spl4_867
    | ~ spl4_722 ),
    inference(avatar_split_clause,[],[f12031,f9933,f12033])).

fof(f9933,plain,
    ( spl4_722
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(k1_xboole_0),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_722])])).

fof(f12031,plain,
    ( r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(sK0))
    | ~ spl4_722 ),
    inference(trivial_inequality_removal,[],[f12030])).

fof(f12030,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(sK0))
    | ~ spl4_722 ),
    inference(superposition,[],[f56,f9935])).

fof(f9935,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(k1_xboole_0),k1_zfmisc_1(sK0))
    | ~ spl4_722 ),
    inference(avatar_component_clause,[],[f9933])).

fof(f10165,plain,
    ( spl4_722
    | ~ spl4_726 ),
    inference(avatar_split_clause,[],[f10163,f10056,f9933])).

fof(f10163,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(k1_xboole_0),k1_zfmisc_1(sK0))
    | ~ spl4_726 ),
    inference(resolution,[],[f10057,f114])).

fof(f114,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X2),X3) ) ),
    inference(resolution,[],[f55,f51])).

fof(f10158,plain,
    ( ~ spl4_723
    | spl4_726 ),
    inference(avatar_contradiction_clause,[],[f10156])).

fof(f10156,plain,
    ( $false
    | ~ spl4_723
    | spl4_726 ),
    inference(unit_resulting_resolution,[],[f33,f9953,f10058,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f10058,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0))
    | spl4_726 ),
    inference(avatar_component_clause,[],[f10056])).

fof(f9953,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl4_723 ),
    inference(avatar_component_clause,[],[f9952])).

fof(f33,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f10141,plain,(
    spl4_723 ),
    inference(avatar_contradiction_clause,[],[f10138])).

fof(f10138,plain,
    ( $false
    | spl4_723 ),
    inference(unit_resulting_resolution,[],[f34,f9954,f53])).

fof(f9954,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | spl4_723 ),
    inference(avatar_component_clause,[],[f9952])).

fof(f492,plain,
    ( ~ spl4_3
    | spl4_39 ),
    inference(avatar_split_clause,[],[f488,f454,f75])).

fof(f488,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl4_39 ),
    inference(resolution,[],[f456,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f456,plain,
    ( ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl4_39 ),
    inference(avatar_component_clause,[],[f454])).

fof(f232,plain,
    ( spl4_19
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f224,f75,f229])).

fof(f224,plain,
    ( sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))
    | ~ spl4_3 ),
    inference(resolution,[],[f40,f77])).

fof(f85,plain,
    ( spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f80,f70,f82])).

fof(f80,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_2 ),
    inference(superposition,[],[f63,f72])).

fof(f63,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f78,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f30,f75])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k7_setfam_1(X0,X1) != k1_tarski(k1_xboole_0)
      & k1_tarski(X0) = X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k7_setfam_1(X0,X1) != k1_tarski(k1_xboole_0)
      & k1_tarski(X0) = X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( k1_tarski(X0) = X1
         => k7_setfam_1(X0,X1) = k1_tarski(k1_xboole_0) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_tarski(X0) = X1
       => k7_setfam_1(X0,X1) = k1_tarski(k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_setfam_1)).

fof(f73,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f31,f70])).

fof(f31,plain,(
    sK1 = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f32,f65])).

fof(f65,plain,
    ( spl4_1
  <=> k1_tarski(k1_xboole_0) = k7_setfam_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f32,plain,(
    k1_tarski(k1_xboole_0) != k7_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

%------------------------------------------------------------------------------
