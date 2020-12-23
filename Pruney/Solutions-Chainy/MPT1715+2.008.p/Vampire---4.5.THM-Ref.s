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
% DateTime   : Thu Dec  3 13:17:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 350 expanded)
%              Number of leaves         :   27 ( 125 expanded)
%              Depth                    :   30
%              Number of atoms          :  581 (1918 expanded)
%              Number of equality atoms :    8 (  16 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f226,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f71,f75,f79,f83,f87,f91,f160,f170,f171,f179,f187,f225])).

fof(f225,plain,
    ( ~ spl5_6
    | ~ spl5_7
    | spl5_14
    | ~ spl5_4
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f224,f89,f69,f156,f81,f77])).

fof(f77,plain,
    ( spl5_6
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f81,plain,
    ( spl5_7
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f156,plain,
    ( spl5_14
  <=> ! [X0] :
        ( r1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f69,plain,
    ( spl5_4
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f89,plain,
    ( spl5_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f224,plain,
    ( ! [X3] :
        ( ~ m1_pre_topc(X3,sK2)
        | r1_tsep_1(X3,sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ m1_pre_topc(X3,sK0) )
    | ~ spl5_4
    | ~ spl5_9 ),
    inference(resolution,[],[f222,f70])).

fof(f70,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f222,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tsep_1(X2,X1)
        | ~ m1_pre_topc(X0,X1)
        | r1_tsep_1(X0,X2)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl5_9 ),
    inference(duplicate_literal_removal,[],[f220])).

fof(f220,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X0,X1)
        | ~ r1_tsep_1(X2,X1)
        | r1_tsep_1(X0,X2)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl5_9 ),
    inference(resolution,[],[f218,f90])).

fof(f90,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f89])).

fof(f218,plain,
    ( ! [X4,X2,X5,X3] :
        ( ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(X2,X3)
        | ~ r1_tsep_1(X4,X3)
        | r1_tsep_1(X2,X4)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X4,sK0)
        | ~ m1_pre_topc(X3,X5)
        | ~ m1_pre_topc(X2,sK0) )
    | ~ spl5_9 ),
    inference(resolution,[],[f216,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f216,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,X2)
        | ~ r1_tsep_1(X1,X2)
        | r1_tsep_1(X0,X1)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X1,sK0) )
    | ~ spl5_9 ),
    inference(duplicate_literal_removal,[],[f214])).

fof(f214,plain,
    ( ! [X2,X0,X1] :
        ( r1_tsep_1(X0,X1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,X2)
        | ~ r1_tsep_1(X1,X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,sK0) )
    | ~ spl5_9 ),
    inference(resolution,[],[f191,f90])).

fof(f191,plain,
    ( ! [X4,X2,X5,X3] :
        ( ~ l1_pre_topc(X5)
        | r1_tsep_1(X3,X2)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X3,X4)
        | ~ r1_tsep_1(X2,X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_pre_topc(X4,sK0)
        | ~ m1_pre_topc(X2,X5)
        | ~ m1_pre_topc(X2,sK0) )
    | ~ spl5_9 ),
    inference(resolution,[],[f154,f47])).

fof(f154,plain,
    ( ! [X2,X3,X1] :
        ( ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(X2,sK0)
        | r1_tsep_1(X3,X2)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X3,X1)
        | ~ r1_tsep_1(X2,X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(X1,sK0) )
    | ~ spl5_9 ),
    inference(resolution,[],[f149,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X0,X1)
      | ~ r1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f92,f46])).

fof(f46,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f50,f46])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f149,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tsep_1(X0,X1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | r1_tsep_1(X2,X1)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X2,X0) )
    | ~ spl5_9 ),
    inference(resolution,[],[f147,f90])).

fof(f147,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(X2,sK0)
        | ~ r1_tsep_1(X2,X1)
        | ~ m1_pre_topc(X1,X3)
        | r1_tsep_1(X0,X1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,X2) )
    | ~ spl5_9 ),
    inference(resolution,[],[f146,f90])).

fof(f146,plain,
    ( ! [X6,X4,X7,X5,X3] :
        ( ~ l1_pre_topc(X7)
        | r1_tsep_1(X3,X5)
        | ~ m1_pre_topc(X4,sK0)
        | ~ r1_tsep_1(X4,X5)
        | ~ m1_pre_topc(X5,X6)
        | ~ l1_pre_topc(X6)
        | ~ m1_pre_topc(X3,X7)
        | ~ m1_pre_topc(X3,X4) )
    | ~ spl5_9 ),
    inference(resolution,[],[f137,f47])).

fof(f137,plain,
    ( ! [X4,X2,X5,X3] :
        ( ~ l1_pre_topc(X4)
        | ~ m1_pre_topc(X4,X2)
        | r1_tsep_1(X4,X3)
        | ~ m1_pre_topc(X2,sK0)
        | ~ r1_tsep_1(X2,X3)
        | ~ m1_pre_topc(X3,X5)
        | ~ l1_pre_topc(X5) )
    | ~ spl5_9 ),
    inference(resolution,[],[f134,f47])).

fof(f134,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X2)
        | ~ r1_tsep_1(X1,X2)
        | ~ m1_pre_topc(X0,X1)
        | r1_tsep_1(X0,X2)
        | ~ m1_pre_topc(X1,sK0)
        | ~ l1_pre_topc(X0) )
    | ~ spl5_9 ),
    inference(resolution,[],[f123,f90])).

fof(f123,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ l1_pre_topc(X5)
      | ~ m1_pre_topc(X2,X3)
      | ~ r1_tsep_1(X3,X4)
      | ~ l1_pre_topc(X4)
      | r1_tsep_1(X2,X4)
      | ~ m1_pre_topc(X3,X5)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f121,f47])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ r1_tsep_1(X0,X2)
      | ~ l1_pre_topc(X2)
      | r1_tsep_1(X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ r1_tsep_1(X0,X2)
      | ~ l1_pre_topc(X2)
      | r1_tsep_1(X1,X2)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f119,f46])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X2)
      | ~ m1_pre_topc(X2,X1)
      | ~ r1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | r1_tsep_1(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X2)
      | ~ m1_pre_topc(X2,X1)
      | ~ r1_tsep_1(X1,X0)
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X2,X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f116,f46])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X0,X2)
      | ~ r1_tsep_1(X2,X1)
      | ~ l1_struct_0(X1)
      | r1_tsep_1(X0,X1) ) ),
    inference(resolution,[],[f115,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X2,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X2)
      | ~ m1_pre_topc(X2,X0) ) ),
    inference(resolution,[],[f113,f43])).

fof(f43,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | r1_tsep_1(X0,X2)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(resolution,[],[f112,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r2_hidden(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(resolution,[],[f48,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(u1_struct_0(X1),k1_zfmisc_1(X2))
      | ~ l1_pre_topc(X1)
      | ~ r1_xboole_0(X2,u1_struct_0(X0))
      | r1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f107,f57])).

fof(f57,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK4(X0,X1),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r1_tarski(sK4(X0,X1),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK4(X0,X1),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( r1_tarski(sK4(X0,X1),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f107,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(u1_struct_0(X2),X4)
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X2)
      | ~ r1_xboole_0(X4,u1_struct_0(X3))
      | r1_tsep_1(X2,X3) ) ),
    inference(resolution,[],[f105,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f104,f46])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | r1_tsep_1(X0,X1)
      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f45,f46])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f187,plain,
    ( ~ spl5_9
    | ~ spl5_8
    | spl5_11 ),
    inference(avatar_split_clause,[],[f182,f99,f85,f89])).

fof(f85,plain,
    ( spl5_8
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f99,plain,
    ( spl5_11
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f182,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_8
    | spl5_11 ),
    inference(resolution,[],[f180,f86])).

fof(f86,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f85])).

fof(f180,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | spl5_11 ),
    inference(resolution,[],[f100,f47])).

fof(f100,plain,
    ( ~ l1_pre_topc(sK1)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f99])).

fof(f179,plain,
    ( ~ spl5_9
    | ~ spl5_6
    | spl5_10 ),
    inference(avatar_split_clause,[],[f178,f96,f77,f89])).

fof(f96,plain,
    ( spl5_10
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f178,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_6
    | spl5_10 ),
    inference(resolution,[],[f172,f78])).

fof(f78,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f172,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0) )
    | spl5_10 ),
    inference(resolution,[],[f97,f47])).

fof(f97,plain,
    ( ~ l1_pre_topc(sK3)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f96])).

fof(f171,plain,
    ( ~ spl5_11
    | ~ spl5_10
    | ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f102,f62,f59,f96,f99])).

fof(f59,plain,
    ( spl5_1
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f62,plain,
    ( spl5_2
  <=> r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f102,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1)
    | spl5_2 ),
    inference(resolution,[],[f63,f93])).

fof(f63,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f170,plain,
    ( ~ spl5_8
    | spl5_1
    | ~ spl5_5
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f167,f156,f73,f59,f85])).

fof(f73,plain,
    ( spl5_5
  <=> m1_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f167,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl5_5
    | ~ spl5_14 ),
    inference(resolution,[],[f157,f74])).

fof(f74,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | r1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f156])).

fof(f160,plain,
    ( spl5_14
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_3
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f153,f89,f66,f81,f77,f156])).

fof(f66,plain,
    ( spl5_3
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f153,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(sK3,sK0)
        | r1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK2) )
    | ~ spl5_3
    | ~ spl5_9 ),
    inference(resolution,[],[f149,f67])).

fof(f67,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f91,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f36,f89])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ r1_tsep_1(sK3,sK1)
      | ~ r1_tsep_1(sK1,sK3) )
    & ( r1_tsep_1(sK3,sK2)
      | r1_tsep_1(sK2,sK3) )
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK3,sK0)
    & m1_pre_topc(sK2,sK0)
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f29,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ r1_tsep_1(X3,X1)
                      | ~ r1_tsep_1(X1,X3) )
                    & ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X2,X3) )
                    & m1_pre_topc(X1,X2)
                    & m1_pre_topc(X3,X0) )
                & m1_pre_topc(X2,X0) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,sK0) )
              & m1_pre_topc(X2,sK0) )
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ r1_tsep_1(X3,X1)
                  | ~ r1_tsep_1(X1,X3) )
                & ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X2,X3) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X3,sK0) )
            & m1_pre_topc(X2,sK0) )
        & m1_pre_topc(X1,sK0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ r1_tsep_1(X3,sK1)
                | ~ r1_tsep_1(sK1,X3) )
              & ( r1_tsep_1(X3,X2)
                | r1_tsep_1(X2,X3) )
              & m1_pre_topc(sK1,X2)
              & m1_pre_topc(X3,sK0) )
          & m1_pre_topc(X2,sK0) )
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ r1_tsep_1(X3,sK1)
              | ~ r1_tsep_1(sK1,X3) )
            & ( r1_tsep_1(X3,X2)
              | r1_tsep_1(X2,X3) )
            & m1_pre_topc(sK1,X2)
            & m1_pre_topc(X3,sK0) )
        & m1_pre_topc(X2,sK0) )
   => ( ? [X3] :
          ( ( ~ r1_tsep_1(X3,sK1)
            | ~ r1_tsep_1(sK1,X3) )
          & ( r1_tsep_1(X3,sK2)
            | r1_tsep_1(sK2,X3) )
          & m1_pre_topc(sK1,sK2)
          & m1_pre_topc(X3,sK0) )
      & m1_pre_topc(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X3] :
        ( ( ~ r1_tsep_1(X3,sK1)
          | ~ r1_tsep_1(sK1,X3) )
        & ( r1_tsep_1(X3,sK2)
          | r1_tsep_1(sK2,X3) )
        & m1_pre_topc(sK1,sK2)
        & m1_pre_topc(X3,sK0) )
   => ( ( ~ r1_tsep_1(sK3,sK1)
        | ~ r1_tsep_1(sK1,sK3) )
      & ( r1_tsep_1(sK3,sK2)
        | r1_tsep_1(sK2,sK3) )
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK3,sK0) ) ),
    introduced(choice_axiom,[])).

% (18349)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ! [X3] :
                    ( m1_pre_topc(X3,X0)
                   => ( m1_pre_topc(X1,X2)
                     => ( ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) )
                        | ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( m1_pre_topc(X1,X2)
                     => ( ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) )
                        | ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( m1_pre_topc(X1,X2)
                     => ( ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) )
                        | ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) )
                      | ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tmap_1)).

fof(f87,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f37,f85])).

fof(f37,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f83,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f38,f81])).

fof(f38,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f79,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f39,f77])).

fof(f39,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f75,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f40,f73])).

fof(f40,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f71,plain,
    ( spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f41,f69,f66])).

fof(f41,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f42,f62,f59])).

fof(f42,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:35:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.45  % (18344)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (18345)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (18345)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f226,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f64,f71,f75,f79,f83,f87,f91,f160,f170,f171,f179,f187,f225])).
% 0.22/0.49  fof(f225,plain,(
% 0.22/0.49    ~spl5_6 | ~spl5_7 | spl5_14 | ~spl5_4 | ~spl5_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f224,f89,f69,f156,f81,f77])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    spl5_6 <=> m1_pre_topc(sK3,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    spl5_7 <=> m1_pre_topc(sK2,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.49  fof(f156,plain,(
% 0.22/0.49    spl5_14 <=> ! [X0] : (r1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X0,sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    spl5_4 <=> r1_tsep_1(sK3,sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    spl5_9 <=> l1_pre_topc(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.49  fof(f224,plain,(
% 0.22/0.49    ( ! [X3] : (~m1_pre_topc(X3,sK2) | r1_tsep_1(X3,sK3) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(X3,sK0)) ) | (~spl5_4 | ~spl5_9)),
% 0.22/0.49    inference(resolution,[],[f222,f70])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    r1_tsep_1(sK3,sK2) | ~spl5_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f69])).
% 0.22/0.49  fof(f222,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r1_tsep_1(X2,X1) | ~m1_pre_topc(X0,X1) | r1_tsep_1(X0,X2) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X0,sK0)) ) | ~spl5_9),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f220])).
% 0.22/0.49  fof(f220,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,X1) | ~r1_tsep_1(X2,X1) | r1_tsep_1(X0,X2) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK0)) ) | ~spl5_9),
% 0.22/0.49    inference(resolution,[],[f218,f90])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    l1_pre_topc(sK0) | ~spl5_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f89])).
% 0.22/0.49  fof(f218,plain,(
% 0.22/0.49    ( ! [X4,X2,X5,X3] : (~l1_pre_topc(X5) | ~m1_pre_topc(X2,X3) | ~r1_tsep_1(X4,X3) | r1_tsep_1(X2,X4) | ~m1_pre_topc(X3,sK0) | ~m1_pre_topc(X4,sK0) | ~m1_pre_topc(X3,X5) | ~m1_pre_topc(X2,sK0)) ) | ~spl5_9),
% 0.22/0.49    inference(resolution,[],[f216,f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.49  fof(f216,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~l1_pre_topc(X2) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X0,X2) | ~r1_tsep_1(X1,X2) | r1_tsep_1(X0,X1) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X1,sK0)) ) | ~spl5_9),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f214])).
% 0.22/0.49  fof(f214,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r1_tsep_1(X0,X1) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X0,X2) | ~r1_tsep_1(X1,X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X1,sK0)) ) | ~spl5_9),
% 0.22/0.49    inference(resolution,[],[f191,f90])).
% 0.22/0.49  fof(f191,plain,(
% 0.22/0.49    ( ! [X4,X2,X5,X3] : (~l1_pre_topc(X5) | r1_tsep_1(X3,X2) | ~m1_pre_topc(X3,sK0) | ~m1_pre_topc(X3,X4) | ~r1_tsep_1(X2,X4) | ~l1_pre_topc(X4) | ~m1_pre_topc(X4,sK0) | ~m1_pre_topc(X2,X5) | ~m1_pre_topc(X2,sK0)) ) | ~spl5_9),
% 0.22/0.49    inference(resolution,[],[f154,f47])).
% 0.22/0.49  fof(f154,plain,(
% 0.22/0.49    ( ! [X2,X3,X1] : (~l1_pre_topc(X2) | ~m1_pre_topc(X2,sK0) | r1_tsep_1(X3,X2) | ~m1_pre_topc(X3,sK0) | ~m1_pre_topc(X3,X1) | ~r1_tsep_1(X2,X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X1,sK0)) ) | ~spl5_9),
% 0.22/0.49    inference(resolution,[],[f149,f93])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tsep_1(X0,X1) | ~r1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1)) )),
% 0.22/0.49    inference(resolution,[],[f92,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_struct_0(X0) | r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_pre_topc(X1)) )),
% 0.22/0.49    inference(resolution,[],[f50,f46])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_struct_0(X1) | ~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0) | ~l1_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 0.22/0.49  fof(f149,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r1_tsep_1(X0,X1) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0) | r1_tsep_1(X2,X1) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X2,X0)) ) | ~spl5_9),
% 0.22/0.49    inference(resolution,[],[f147,f90])).
% 0.22/0.49  fof(f147,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X3) | ~m1_pre_topc(X2,sK0) | ~r1_tsep_1(X2,X1) | ~m1_pre_topc(X1,X3) | r1_tsep_1(X0,X1) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X0,X2)) ) | ~spl5_9),
% 0.22/0.49    inference(resolution,[],[f146,f90])).
% 0.22/0.49  fof(f146,plain,(
% 0.22/0.49    ( ! [X6,X4,X7,X5,X3] : (~l1_pre_topc(X7) | r1_tsep_1(X3,X5) | ~m1_pre_topc(X4,sK0) | ~r1_tsep_1(X4,X5) | ~m1_pre_topc(X5,X6) | ~l1_pre_topc(X6) | ~m1_pre_topc(X3,X7) | ~m1_pre_topc(X3,X4)) ) | ~spl5_9),
% 0.22/0.49    inference(resolution,[],[f137,f47])).
% 0.22/0.49  fof(f137,plain,(
% 0.22/0.49    ( ! [X4,X2,X5,X3] : (~l1_pre_topc(X4) | ~m1_pre_topc(X4,X2) | r1_tsep_1(X4,X3) | ~m1_pre_topc(X2,sK0) | ~r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X5) | ~l1_pre_topc(X5)) ) | ~spl5_9),
% 0.22/0.49    inference(resolution,[],[f134,f47])).
% 0.22/0.49  fof(f134,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~l1_pre_topc(X2) | ~r1_tsep_1(X1,X2) | ~m1_pre_topc(X0,X1) | r1_tsep_1(X0,X2) | ~m1_pre_topc(X1,sK0) | ~l1_pre_topc(X0)) ) | ~spl5_9),
% 0.22/0.49    inference(resolution,[],[f123,f90])).
% 0.22/0.49  fof(f123,plain,(
% 0.22/0.49    ( ! [X4,X2,X5,X3] : (~l1_pre_topc(X5) | ~m1_pre_topc(X2,X3) | ~r1_tsep_1(X3,X4) | ~l1_pre_topc(X4) | r1_tsep_1(X2,X4) | ~m1_pre_topc(X3,X5) | ~l1_pre_topc(X2)) )),
% 0.22/0.49    inference(resolution,[],[f121,f47])).
% 0.22/0.49  fof(f121,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~r1_tsep_1(X0,X2) | ~l1_pre_topc(X2) | r1_tsep_1(X1,X2)) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f120])).
% 0.22/0.49  fof(f120,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~r1_tsep_1(X0,X2) | ~l1_pre_topc(X2) | r1_tsep_1(X1,X2) | ~l1_pre_topc(X2)) )),
% 0.22/0.49    inference(resolution,[],[f119,f46])).
% 0.22/0.49  fof(f119,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X2) | ~m1_pre_topc(X2,X1) | ~r1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | r1_tsep_1(X2,X0)) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f118])).
% 0.22/0.49  fof(f118,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X2) | ~m1_pre_topc(X2,X1) | ~r1_tsep_1(X1,X0) | ~l1_struct_0(X0) | r1_tsep_1(X2,X0) | ~l1_pre_topc(X1)) )),
% 0.22/0.49    inference(resolution,[],[f116,f46])).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~l1_struct_0(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X2) | ~l1_pre_topc(X0) | ~m1_pre_topc(X0,X2) | ~r1_tsep_1(X2,X1) | ~l1_struct_0(X1) | r1_tsep_1(X0,X1)) )),
% 0.22/0.49    inference(resolution,[],[f115,f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).
% 0.22/0.49  fof(f115,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | r1_tsep_1(X2,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~l1_pre_topc(X2) | ~m1_pre_topc(X2,X0)) )),
% 0.22/0.49    inference(resolution,[],[f113,f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.22/0.49  fof(f113,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1))) | ~r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | r1_tsep_1(X0,X2) | ~l1_pre_topc(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~m1_pre_topc(X0,X1)) )),
% 0.22/0.49    inference(resolution,[],[f112,f103])).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X0,X1)) )),
% 0.22/0.49    inference(resolution,[],[f48,f49])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.49    inference(flattening,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.49  fof(f112,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(u1_struct_0(X1),k1_zfmisc_1(X2)) | ~l1_pre_topc(X1) | ~r1_xboole_0(X2,u1_struct_0(X0)) | r1_tsep_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(resolution,[],[f107,f57])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(equality_resolution,[],[f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.50    inference(rectify,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    ( ! [X4,X2,X3] : (~r1_tarski(u1_struct_0(X2),X4) | ~l1_pre_topc(X3) | ~l1_pre_topc(X2) | ~r1_xboole_0(X4,u1_struct_0(X3)) | r1_tsep_1(X2,X3)) )),
% 0.22/0.50    inference(resolution,[],[f105,f55])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | r1_tsep_1(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(resolution,[],[f104,f46])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_struct_0(X0) | r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1)) )),
% 0.22/0.50    inference(resolution,[],[f45,f46])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_struct_0(X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | r1_tsep_1(X0,X1) | ~l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f187,plain,(
% 0.22/0.50    ~spl5_9 | ~spl5_8 | spl5_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f182,f99,f85,f89])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    spl5_8 <=> m1_pre_topc(sK1,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    spl5_11 <=> l1_pre_topc(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.50  fof(f182,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | (~spl5_8 | spl5_11)),
% 0.22/0.50    inference(resolution,[],[f180,f86])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    m1_pre_topc(sK1,sK0) | ~spl5_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f85])).
% 0.22/0.50  fof(f180,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) ) | spl5_11),
% 0.22/0.50    inference(resolution,[],[f100,f47])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    ~l1_pre_topc(sK1) | spl5_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f99])).
% 0.22/0.50  fof(f179,plain,(
% 0.22/0.50    ~spl5_9 | ~spl5_6 | spl5_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f178,f96,f77,f89])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    spl5_10 <=> l1_pre_topc(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.50  fof(f178,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | (~spl5_6 | spl5_10)),
% 0.22/0.50    inference(resolution,[],[f172,f78])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    m1_pre_topc(sK3,sK0) | ~spl5_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f77])).
% 0.22/0.50  fof(f172,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0)) ) | spl5_10),
% 0.22/0.50    inference(resolution,[],[f97,f47])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    ~l1_pre_topc(sK3) | spl5_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f96])).
% 0.22/0.50  fof(f171,plain,(
% 0.22/0.50    ~spl5_11 | ~spl5_10 | ~spl5_1 | spl5_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f102,f62,f59,f96,f99])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    spl5_1 <=> r1_tsep_1(sK1,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    spl5_2 <=> r1_tsep_1(sK3,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    ~r1_tsep_1(sK1,sK3) | ~l1_pre_topc(sK3) | ~l1_pre_topc(sK1) | spl5_2),
% 0.22/0.50    inference(resolution,[],[f63,f93])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ~r1_tsep_1(sK3,sK1) | spl5_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f62])).
% 0.22/0.50  fof(f170,plain,(
% 0.22/0.50    ~spl5_8 | spl5_1 | ~spl5_5 | ~spl5_14),
% 0.22/0.50    inference(avatar_split_clause,[],[f167,f156,f73,f59,f85])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    spl5_5 <=> m1_pre_topc(sK1,sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.50  fof(f167,plain,(
% 0.22/0.50    r1_tsep_1(sK1,sK3) | ~m1_pre_topc(sK1,sK0) | (~spl5_5 | ~spl5_14)),
% 0.22/0.50    inference(resolution,[],[f157,f74])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    m1_pre_topc(sK1,sK2) | ~spl5_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f73])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_pre_topc(X0,sK2) | r1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK0)) ) | ~spl5_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f156])).
% 0.22/0.50  fof(f160,plain,(
% 0.22/0.50    spl5_14 | ~spl5_6 | ~spl5_7 | ~spl5_3 | ~spl5_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f153,f89,f66,f81,f77,f156])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    spl5_3 <=> r1_tsep_1(sK2,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.50  fof(f153,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK3,sK0) | r1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X0,sK2)) ) | (~spl5_3 | ~spl5_9)),
% 0.22/0.50    inference(resolution,[],[f149,f67])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    r1_tsep_1(sK2,sK3) | ~spl5_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f66])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    spl5_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f36,f89])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    l1_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ((((~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)) & (r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0)) & m1_pre_topc(sK2,sK0)) & m1_pre_topc(sK1,sK0)) & l1_pre_topc(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f29,f28,f27,f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(X1,sK0)) & l1_pre_topc(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(X1,sK0)) => (? [X2] : (? [X3] : ((~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,sK0)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(sK1,sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ? [X2] : (? [X3] : ((~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,sK0)) & m1_pre_topc(X2,sK0)) => (? [X3] : ((~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & (r1_tsep_1(X3,sK2) | r1_tsep_1(sK2,X3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X3,sK0)) & m1_pre_topc(sK2,sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ? [X3] : ((~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & (r1_tsep_1(X3,sK2) | r1_tsep_1(sK2,X3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X3,sK0)) => ((~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)) & (r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  % (18349)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3))) & m1_pre_topc(X1,X2)) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.50  fof(f11,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f10])).
% 0.22/0.50  fof(f10,conjecture,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tmap_1)).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    spl5_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f37,f85])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    m1_pre_topc(sK1,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    spl5_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f38,f81])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    m1_pre_topc(sK2,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    spl5_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f39,f77])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    m1_pre_topc(sK3,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    spl5_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f40,f73])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    m1_pre_topc(sK1,sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    spl5_3 | spl5_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f41,f69,f66])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ~spl5_1 | ~spl5_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f42,f62,f59])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (18345)------------------------------
% 0.22/0.50  % (18345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (18345)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (18345)Memory used [KB]: 10746
% 0.22/0.50  % (18345)Time elapsed: 0.077 s
% 0.22/0.50  % (18345)------------------------------
% 0.22/0.50  % (18345)------------------------------
% 0.22/0.50  % (18349)Refutation not found, incomplete strategy% (18349)------------------------------
% 0.22/0.50  % (18349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (18349)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (18349)Memory used [KB]: 6140
% 0.22/0.50  % (18349)Time elapsed: 0.085 s
% 0.22/0.50  % (18349)------------------------------
% 0.22/0.50  % (18349)------------------------------
% 0.22/0.50  % (18334)Success in time 0.134 s
%------------------------------------------------------------------------------
