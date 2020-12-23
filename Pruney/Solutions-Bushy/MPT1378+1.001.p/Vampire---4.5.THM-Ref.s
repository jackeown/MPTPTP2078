%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1378+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:50 EST 2020

% Result     : Theorem 2.14s
% Output     : Refutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 365 expanded)
%              Number of leaves         :   40 ( 168 expanded)
%              Depth                    :   11
%              Number of atoms          :  551 (1569 expanded)
%              Number of equality atoms :   19 (  45 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2472,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f95,f100,f105,f110,f115,f120,f125,f380,f385,f487,f648,f701,f713,f773,f1563,f1637,f1684,f1806,f2462,f2471])).

fof(f2471,plain,
    ( ~ spl8_181
    | ~ spl8_171
    | ~ spl8_183 ),
    inference(avatar_split_clause,[],[f2444,f1770,f1560,f1681])).

fof(f1681,plain,
    ( spl8_181
  <=> v1_xboole_0(k1_tops_1(sK2,k2_xboole_0(sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_181])])).

fof(f1560,plain,
    ( spl8_171
  <=> r2_hidden(sK3,k1_tops_1(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_171])])).

fof(f1770,plain,
    ( spl8_183
  <=> r1_tarski(k2_xboole_0(k1_tops_1(sK2,sK4),k1_tops_1(sK2,sK5)),k1_tops_1(sK2,k2_xboole_0(sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_183])])).

fof(f2444,plain,
    ( ~ v1_xboole_0(k1_tops_1(sK2,k2_xboole_0(sK4,sK5)))
    | ~ spl8_171
    | ~ spl8_183 ),
    inference(unit_resulting_resolution,[],[f2086,f1772,f193])).

fof(f193,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | sP7(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f79,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f79,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP7(X1) ) ),
    inference(cnf_transformation,[],[f79_D])).

fof(f79_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP7(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f1772,plain,
    ( r1_tarski(k2_xboole_0(k1_tops_1(sK2,sK4),k1_tops_1(sK2,sK5)),k1_tops_1(sK2,k2_xboole_0(sK4,sK5)))
    | ~ spl8_183 ),
    inference(avatar_component_clause,[],[f1770])).

fof(f2086,plain,
    ( ! [X4] : ~ sP7(k2_xboole_0(k1_tops_1(sK2,sK4),X4))
    | ~ spl8_171 ),
    inference(superposition,[],[f2076,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f2076,plain,
    ( ! [X0] : ~ sP7(k2_xboole_0(X0,k1_tops_1(sK2,sK4)))
    | ~ spl8_171 ),
    inference(unit_resulting_resolution,[],[f1622,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP7(X1) ) ),
    inference(general_splitting,[],[f77,f79_D])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f1622,plain,
    ( ! [X0] : r2_hidden(sK3,k2_xboole_0(X0,k1_tops_1(sK2,sK4)))
    | ~ spl8_171 ),
    inference(unit_resulting_resolution,[],[f78,f1592,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X1,X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sP0(X1,sK6(X0,X1,X2),X0)
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sP0(X1,sK6(X0,X1,X2),X0)
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X1,X3,X0) )
            & ( sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f1592,plain,
    ( ! [X0] : sP0(k1_tops_1(sK2,sK4),sK3,X0)
    | ~ spl8_171 ),
    inference(unit_resulting_resolution,[],[f1562,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r2_hidden(X1,X0)
          & ~ r2_hidden(X1,X2) ) )
      & ( r2_hidden(X1,X0)
        | r2_hidden(X1,X2)
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X3,X0) ) )
      & ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0)
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X3,X0) ) )
      & ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0)
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1562,plain,
    ( r2_hidden(sK3,k1_tops_1(sK2,sK4))
    | ~ spl8_171 ),
    inference(avatar_component_clause,[],[f1560])).

fof(f78,plain,(
    ! [X0,X1] : sP1(X0,X1,k2_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f3,f31,f30])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f2462,plain,
    ( spl8_180
    | ~ spl8_171
    | ~ spl8_183 ),
    inference(avatar_split_clause,[],[f2440,f1770,f1560,f1677])).

fof(f1677,plain,
    ( spl8_180
  <=> m1_subset_1(sK3,k1_tops_1(sK2,k2_xboole_0(sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_180])])).

fof(f2440,plain,
    ( m1_subset_1(sK3,k1_tops_1(sK2,k2_xboole_0(sK4,sK5)))
    | ~ spl8_171
    | ~ spl8_183 ),
    inference(unit_resulting_resolution,[],[f1623,f1772,f260])).

fof(f260,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | ~ r2_hidden(X0,X2)
      | m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f65,f64])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f1623,plain,
    ( ! [X0] : r2_hidden(sK3,k2_xboole_0(k1_tops_1(sK2,sK4),X0))
    | ~ spl8_171 ),
    inference(unit_resulting_resolution,[],[f126,f1592,f69])).

fof(f126,plain,(
    ! [X0,X1] : sP1(X0,X1,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f78,f60])).

fof(f1806,plain,
    ( spl8_183
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_53
    | ~ spl8_63 ),
    inference(avatar_split_clause,[],[f1805,f698,f645,f112,f102,f97,f1770])).

fof(f97,plain,
    ( spl8_4
  <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f102,plain,
    ( spl8_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f112,plain,
    ( spl8_7
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f645,plain,
    ( spl8_53
  <=> k4_subset_1(u1_struct_0(sK2),sK5,sK4) = k2_xboole_0(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).

fof(f698,plain,
    ( spl8_63
  <=> k4_subset_1(u1_struct_0(sK2),k1_tops_1(sK2,sK5),k1_tops_1(sK2,sK4)) = k2_xboole_0(k1_tops_1(sK2,sK4),k1_tops_1(sK2,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_63])])).

fof(f1805,plain,
    ( r1_tarski(k2_xboole_0(k1_tops_1(sK2,sK4),k1_tops_1(sK2,sK5)),k1_tops_1(sK2,k2_xboole_0(sK4,sK5)))
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_53
    | ~ spl8_63 ),
    inference(forward_demodulation,[],[f1804,f700])).

fof(f700,plain,
    ( k4_subset_1(u1_struct_0(sK2),k1_tops_1(sK2,sK5),k1_tops_1(sK2,sK4)) = k2_xboole_0(k1_tops_1(sK2,sK4),k1_tops_1(sK2,sK5))
    | ~ spl8_63 ),
    inference(avatar_component_clause,[],[f698])).

fof(f1804,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK2),k1_tops_1(sK2,sK5),k1_tops_1(sK2,sK4)),k1_tops_1(sK2,k2_xboole_0(sK4,sK5)))
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_53 ),
    inference(forward_demodulation,[],[f1747,f647])).

fof(f647,plain,
    ( k4_subset_1(u1_struct_0(sK2),sK5,sK4) = k2_xboole_0(sK4,sK5)
    | ~ spl8_53 ),
    inference(avatar_component_clause,[],[f645])).

fof(f1747,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK2),k1_tops_1(sK2,sK5),k1_tops_1(sK2,sK4)),k1_tops_1(sK2,k4_subset_1(u1_struct_0(sK2),sK5,sK4)))
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f114,f99,f104,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tops_1)).

fof(f104,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f99,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f97])).

fof(f114,plain,
    ( l1_pre_topc(sK2)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f112])).

fof(f1684,plain,
    ( ~ spl8_180
    | spl8_181
    | spl8_178 ),
    inference(avatar_split_clause,[],[f1667,f1634,f1681,f1677])).

fof(f1634,plain,
    ( spl8_178
  <=> r2_hidden(sK3,k1_tops_1(sK2,k2_xboole_0(sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_178])])).

fof(f1667,plain,
    ( v1_xboole_0(k1_tops_1(sK2,k2_xboole_0(sK4,sK5)))
    | ~ m1_subset_1(sK3,k1_tops_1(sK2,k2_xboole_0(sK4,sK5)))
    | spl8_178 ),
    inference(resolution,[],[f1636,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f1636,plain,
    ( ~ r2_hidden(sK3,k1_tops_1(sK2,k2_xboole_0(sK4,sK5)))
    | spl8_178 ),
    inference(avatar_component_clause,[],[f1634])).

fof(f1637,plain,
    ( ~ spl8_178
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | spl8_9
    | spl8_65
    | ~ spl8_74 ),
    inference(avatar_split_clause,[],[f1625,f770,f710,f122,f117,f112,f107,f1634])).

fof(f107,plain,
    ( spl8_6
  <=> m1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f117,plain,
    ( spl8_8
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f122,plain,
    ( spl8_9
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f710,plain,
    ( spl8_65
  <=> m1_connsp_2(k2_xboole_0(sK4,sK5),sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_65])])).

fof(f770,plain,
    ( spl8_74
  <=> m1_subset_1(k2_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_74])])).

fof(f1625,plain,
    ( ~ r2_hidden(sK3,k1_tops_1(sK2,k2_xboole_0(sK4,sK5)))
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | spl8_9
    | spl8_65
    | ~ spl8_74 ),
    inference(unit_resulting_resolution,[],[f124,f119,f114,f109,f712,f772,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f772,plain,
    ( m1_subset_1(k2_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_74 ),
    inference(avatar_component_clause,[],[f770])).

fof(f712,plain,
    ( ~ m1_connsp_2(k2_xboole_0(sK4,sK5),sK2,sK3)
    | spl8_65 ),
    inference(avatar_component_clause,[],[f710])).

fof(f109,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f119,plain,
    ( v2_pre_topc(sK2)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f117])).

fof(f124,plain,
    ( ~ v2_struct_0(sK2)
    | spl8_9 ),
    inference(avatar_component_clause,[],[f122])).

fof(f1563,plain,
    ( spl8_171
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | spl8_9 ),
    inference(avatar_split_clause,[],[f1551,f122,f117,f112,f107,f102,f92,f1560])).

fof(f92,plain,
    ( spl8_3
  <=> m1_connsp_2(sK4,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f1551,plain,
    ( r2_hidden(sK3,k1_tops_1(sK2,sK4))
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | spl8_9 ),
    inference(unit_resulting_resolution,[],[f124,f119,f114,f109,f94,f104,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f94,plain,
    ( m1_connsp_2(sK4,sK2,sK3)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f773,plain,
    ( spl8_74
    | ~ spl8_37
    | ~ spl8_53 ),
    inference(avatar_split_clause,[],[f768,f645,f484,f770])).

fof(f484,plain,
    ( spl8_37
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK2),sK5,sK4),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f768,plain,
    ( m1_subset_1(k2_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_37
    | ~ spl8_53 ),
    inference(backward_demodulation,[],[f486,f647])).

fof(f486,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK2),sK5,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_37 ),
    inference(avatar_component_clause,[],[f484])).

fof(f713,plain,
    ( ~ spl8_65
    | spl8_1
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f708,f102,f97,f82,f710])).

fof(f82,plain,
    ( spl8_1
  <=> m1_connsp_2(k4_subset_1(u1_struct_0(sK2),sK4,sK5),sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f708,plain,
    ( ~ m1_connsp_2(k2_xboole_0(sK4,sK5),sK2,sK3)
    | spl8_1
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f707,f104])).

fof(f707,plain,
    ( ~ m1_connsp_2(k2_xboole_0(sK4,sK5),sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl8_1
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f618,f99])).

fof(f618,plain,
    ( ~ m1_connsp_2(k2_xboole_0(sK4,sK5),sK2,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl8_1 ),
    inference(superposition,[],[f84,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f84,plain,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK2),sK4,sK5),sK2,sK3)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f701,plain,
    ( spl8_63
    | ~ spl8_27
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f696,f382,f377,f698])).

fof(f377,plain,
    ( spl8_27
  <=> m1_subset_1(k1_tops_1(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f382,plain,
    ( spl8_28
  <=> m1_subset_1(k1_tops_1(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f696,plain,
    ( k4_subset_1(u1_struct_0(sK2),k1_tops_1(sK2,sK5),k1_tops_1(sK2,sK4)) = k2_xboole_0(k1_tops_1(sK2,sK4),k1_tops_1(sK2,sK5))
    | ~ spl8_27
    | ~ spl8_28 ),
    inference(forward_demodulation,[],[f603,f60])).

fof(f603,plain,
    ( k4_subset_1(u1_struct_0(sK2),k1_tops_1(sK2,sK5),k1_tops_1(sK2,sK4)) = k2_xboole_0(k1_tops_1(sK2,sK5),k1_tops_1(sK2,sK4))
    | ~ spl8_27
    | ~ spl8_28 ),
    inference(unit_resulting_resolution,[],[f384,f379,f67])).

fof(f379,plain,
    ( m1_subset_1(k1_tops_1(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f377])).

fof(f384,plain,
    ( m1_subset_1(k1_tops_1(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f382])).

fof(f648,plain,
    ( spl8_53
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f643,f102,f97,f645])).

fof(f643,plain,
    ( k4_subset_1(u1_struct_0(sK2),sK5,sK4) = k2_xboole_0(sK4,sK5)
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f613,f60])).

fof(f613,plain,
    ( k4_subset_1(u1_struct_0(sK2),sK5,sK4) = k2_xboole_0(sK5,sK4)
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f99,f104,f67])).

fof(f487,plain,
    ( spl8_37
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f454,f102,f97,f484])).

fof(f454,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK2),sK5,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f99,f104,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f385,plain,
    ( spl8_28
    | ~ spl8_4
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f370,f112,f97,f382])).

fof(f370,plain,
    ( m1_subset_1(k1_tops_1(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_4
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f114,f99,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f380,plain,
    ( spl8_27
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f371,f112,f102,f377])).

fof(f371,plain,
    ( m1_subset_1(k1_tops_1(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f114,f104,f62])).

fof(f125,plain,(
    ~ spl8_9 ),
    inference(avatar_split_clause,[],[f48,f122])).

fof(f48,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK2),sK4,sK5),sK2,sK3)
    & m1_connsp_2(sK5,sK2,sK3)
    & m1_connsp_2(sK4,sK2,sK3)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f15,f36,f35,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                    & m1_connsp_2(X3,X0,X1)
                    & m1_connsp_2(X2,X0,X1)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK2),X2,X3),sK2,X1)
                  & m1_connsp_2(X3,sK2,X1)
                  & m1_connsp_2(X2,sK2,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK2),X2,X3),sK2,X1)
                & m1_connsp_2(X3,sK2,X1)
                & m1_connsp_2(X2,sK2,X1)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
        & m1_subset_1(X1,u1_struct_0(sK2)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK2),X2,X3),sK2,sK3)
              & m1_connsp_2(X3,sK2,sK3)
              & m1_connsp_2(X2,sK2,sK3)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK2),X2,X3),sK2,sK3)
            & m1_connsp_2(X3,sK2,sK3)
            & m1_connsp_2(X2,sK2,sK3)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ? [X3] :
          ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK2),sK4,X3),sK2,sK3)
          & m1_connsp_2(X3,sK2,sK3)
          & m1_connsp_2(sK4,sK2,sK3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X3] :
        ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK2),sK4,X3),sK2,sK3)
        & m1_connsp_2(X3,sK2,sK3)
        & m1_connsp_2(sK4,sK2,sK3)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK2),sK4,sK5),sK2,sK3)
      & m1_connsp_2(sK5,sK2,sK3)
      & m1_connsp_2(sK4,sK2,sK3)
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_connsp_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_connsp_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( m1_connsp_2(X3,X0,X1)
                        & m1_connsp_2(X2,X0,X1) )
                     => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                   => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_connsp_2)).

fof(f120,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f49,f117])).

fof(f49,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f115,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f50,f112])).

fof(f50,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f110,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f51,f107])).

fof(f51,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f105,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f52,f102])).

fof(f52,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f37])).

fof(f100,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f53,f97])).

fof(f53,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f37])).

fof(f95,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f54,f92])).

fof(f54,plain,(
    m1_connsp_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f85,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f56,f82])).

fof(f56,plain,(
    ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK2),sK4,sK5),sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

%------------------------------------------------------------------------------
