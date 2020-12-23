%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 155 expanded)
%              Number of leaves         :   24 (  70 expanded)
%              Depth                    :    8
%              Number of atoms          :  251 ( 395 expanded)
%              Number of equality atoms :   32 (  49 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f474,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f53,f58,f63,f205,f211,f223,f227,f269,f274,f293,f347,f441,f468])).

fof(f468,plain,
    ( spl2_26
    | ~ spl2_58 ),
    inference(avatar_split_clause,[],[f448,f438,f208])).

fof(f208,plain,
    ( spl2_26
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f438,plain,
    ( spl2_58
  <=> sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).

fof(f448,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_58 ),
    inference(superposition,[],[f64,f440])).

fof(f440,plain,
    ( sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_58 ),
    inference(avatar_component_clause,[],[f438])).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f34,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f441,plain,
    ( spl2_58
    | ~ spl2_27
    | ~ spl2_36
    | ~ spl2_43 ),
    inference(avatar_split_clause,[],[f436,f344,f290,f216,f438])).

fof(f216,plain,
    ( spl2_27
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f290,plain,
    ( spl2_36
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f344,plain,
    ( spl2_43
  <=> sK1 = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f436,plain,
    ( sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_27
    | ~ spl2_36
    | ~ spl2_43 ),
    inference(forward_demodulation,[],[f429,f346])).

fof(f346,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_43 ),
    inference(avatar_component_clause,[],[f344])).

fof(f429,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_27
    | ~ spl2_36 ),
    inference(resolution,[],[f235,f292])).

fof(f292,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f290])).

fof(f235,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0) = k2_xboole_0(k1_tops_1(sK0,sK1),X0) )
    | ~ spl2_27 ),
    inference(resolution,[],[f217,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f217,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f216])).

fof(f347,plain,
    ( spl2_43
    | ~ spl2_1
    | ~ spl2_25
    | ~ spl2_27
    | ~ spl2_33 ),
    inference(avatar_split_clause,[],[f342,f261,f216,f202,f45,f344])).

fof(f45,plain,
    ( spl2_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f202,plain,
    ( spl2_25
  <=> sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f261,plain,
    ( spl2_33
  <=> k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f342,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_25
    | ~ spl2_27
    | ~ spl2_33 ),
    inference(forward_demodulation,[],[f341,f204])).

fof(f204,plain,
    ( sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f202])).

fof(f341,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_27
    | ~ spl2_33 ),
    inference(forward_demodulation,[],[f332,f263])).

fof(f263,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k1_tops_1(sK0,sK1))
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f261])).

fof(f332,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1)))
    | ~ spl2_1
    | ~ spl2_27 ),
    inference(resolution,[],[f270,f217])).

fof(f270,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) )
    | ~ spl2_1 ),
    inference(resolution,[],[f31,f47])).

fof(f47,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f293,plain,
    ( ~ spl2_1
    | ~ spl2_27
    | spl2_36
    | ~ spl2_33 ),
    inference(avatar_split_clause,[],[f282,f261,f290,f216,f45])).

fof(f282,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_33 ),
    inference(superposition,[],[f37,f263])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f274,plain,
    ( ~ spl2_1
    | ~ spl2_4
    | spl2_34 ),
    inference(avatar_split_clause,[],[f272,f265,f60,f45])).

fof(f60,plain,
    ( spl2_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f265,plain,
    ( spl2_34
  <=> r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f272,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_34 ),
    inference(resolution,[],[f267,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_tops_1)).

fof(f267,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | spl2_34 ),
    inference(avatar_component_clause,[],[f265])).

fof(f269,plain,
    ( spl2_33
    | ~ spl2_34
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f259,f220,f265,f261])).

fof(f220,plain,
    ( spl2_28
  <=> r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f259,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k1_tops_1(sK0,sK1))
    | ~ spl2_28 ),
    inference(resolution,[],[f222,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f222,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1)))
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f220])).

fof(f227,plain,
    ( ~ spl2_1
    | ~ spl2_4
    | spl2_27 ),
    inference(avatar_split_clause,[],[f225,f216,f60,f45])).

fof(f225,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_27 ),
    inference(resolution,[],[f218,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f218,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_27 ),
    inference(avatar_component_clause,[],[f216])).

fof(f223,plain,
    ( ~ spl2_1
    | ~ spl2_27
    | spl2_28
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f213,f202,f220,f216,f45])).

fof(f213,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_25 ),
    inference(superposition,[],[f30,f204])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tops_1)).

fof(f211,plain,
    ( ~ spl2_26
    | spl2_2
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f206,f202,f50,f208])).

fof(f50,plain,
    ( spl2_2
  <=> r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f206,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | spl2_2
    | ~ spl2_25 ),
    inference(backward_demodulation,[],[f52,f204])).

fof(f52,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f205,plain,
    ( ~ spl2_4
    | spl2_25
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f200,f55,f45,f202,f60])).

fof(f55,plain,
    ( spl2_3
  <=> v5_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f200,plain,
    ( sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(resolution,[],[f199,f57])).

fof(f57,plain,
    ( v5_tops_1(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f199,plain,
    ( ! [X0] :
        ( ~ v5_tops_1(X0,sK0)
        | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_1 ),
    inference(resolution,[],[f33,f47])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ v5_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

fof(f63,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f25,f60])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v5_tops_1(X1,X0)
             => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tops_1)).

fof(f58,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f26,f55])).

fof(f26,plain,(
    v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f27,f50])).

fof(f27,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f48,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f28,f45])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:55:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (688)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.49  % (675)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.50  % (671)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (670)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (682)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (672)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (668)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (676)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (689)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (679)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (685)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (692)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (669)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (678)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (690)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (681)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (673)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (677)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (683)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (680)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (674)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.53  % (683)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f474,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f48,f53,f58,f63,f205,f211,f223,f227,f269,f274,f293,f347,f441,f468])).
% 0.21/0.53  fof(f468,plain,(
% 0.21/0.53    spl2_26 | ~spl2_58),
% 0.21/0.53    inference(avatar_split_clause,[],[f448,f438,f208])).
% 0.21/0.53  fof(f208,plain,(
% 0.21/0.53    spl2_26 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.21/0.53  fof(f438,plain,(
% 0.21/0.53    spl2_58 <=> sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).
% 0.21/0.53  fof(f448,plain,(
% 0.21/0.53    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_58),
% 0.21/0.53    inference(superposition,[],[f64,f440])).
% 0.21/0.53  fof(f440,plain,(
% 0.21/0.53    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl2_58),
% 0.21/0.53    inference(avatar_component_clause,[],[f438])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 0.21/0.53    inference(superposition,[],[f34,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.53  fof(f441,plain,(
% 0.21/0.53    spl2_58 | ~spl2_27 | ~spl2_36 | ~spl2_43),
% 0.21/0.53    inference(avatar_split_clause,[],[f436,f344,f290,f216,f438])).
% 0.21/0.53  fof(f216,plain,(
% 0.21/0.53    spl2_27 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.21/0.53  fof(f290,plain,(
% 0.21/0.53    spl2_36 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 0.21/0.53  fof(f344,plain,(
% 0.21/0.53    spl2_43 <=> sK1 = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 0.21/0.53  fof(f436,plain,(
% 0.21/0.53    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | (~spl2_27 | ~spl2_36 | ~spl2_43)),
% 0.21/0.53    inference(forward_demodulation,[],[f429,f346])).
% 0.21/0.53  fof(f346,plain,(
% 0.21/0.53    sK1 = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl2_43),
% 0.21/0.53    inference(avatar_component_clause,[],[f344])).
% 0.21/0.53  fof(f429,plain,(
% 0.21/0.53    k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | (~spl2_27 | ~spl2_36)),
% 0.21/0.53    inference(resolution,[],[f235,f292])).
% 0.21/0.53  fof(f292,plain,(
% 0.21/0.53    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_36),
% 0.21/0.53    inference(avatar_component_clause,[],[f290])).
% 0.21/0.53  fof(f235,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0) = k2_xboole_0(k1_tops_1(sK0,sK1),X0)) ) | ~spl2_27),
% 0.21/0.53    inference(resolution,[],[f217,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(flattening,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.21/0.53  fof(f217,plain,(
% 0.21/0.53    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_27),
% 0.21/0.53    inference(avatar_component_clause,[],[f216])).
% 0.21/0.53  fof(f347,plain,(
% 0.21/0.53    spl2_43 | ~spl2_1 | ~spl2_25 | ~spl2_27 | ~spl2_33),
% 0.21/0.53    inference(avatar_split_clause,[],[f342,f261,f216,f202,f45,f344])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    spl2_1 <=> l1_pre_topc(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.53  fof(f202,plain,(
% 0.21/0.53    spl2_25 <=> sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.21/0.53  fof(f261,plain,(
% 0.21/0.53    spl2_33 <=> k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k1_tops_1(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 0.21/0.53  fof(f342,plain,(
% 0.21/0.53    sK1 = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | (~spl2_1 | ~spl2_25 | ~spl2_27 | ~spl2_33)),
% 0.21/0.53    inference(forward_demodulation,[],[f341,f204])).
% 0.21/0.53  fof(f204,plain,(
% 0.21/0.53    sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) | ~spl2_25),
% 0.21/0.53    inference(avatar_component_clause,[],[f202])).
% 0.21/0.53  fof(f341,plain,(
% 0.21/0.53    k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | (~spl2_1 | ~spl2_27 | ~spl2_33)),
% 0.21/0.53    inference(forward_demodulation,[],[f332,f263])).
% 0.21/0.53  fof(f263,plain,(
% 0.21/0.53    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k1_tops_1(sK0,sK1)) | ~spl2_33),
% 0.21/0.53    inference(avatar_component_clause,[],[f261])).
% 0.21/0.53  fof(f332,plain,(
% 0.21/0.53    k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) | (~spl2_1 | ~spl2_27)),
% 0.21/0.53    inference(resolution,[],[f270,f217])).
% 0.21/0.53  fof(f270,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) ) | ~spl2_1),
% 0.21/0.53    inference(resolution,[],[f31,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    l1_pre_topc(sK0) | ~spl2_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f45])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 0.21/0.53  fof(f293,plain,(
% 0.21/0.53    ~spl2_1 | ~spl2_27 | spl2_36 | ~spl2_33),
% 0.21/0.53    inference(avatar_split_clause,[],[f282,f261,f290,f216,f45])).
% 0.21/0.53  fof(f282,plain,(
% 0.21/0.53    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_33),
% 0.21/0.53    inference(superposition,[],[f37,f263])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.21/0.53  fof(f274,plain,(
% 0.21/0.53    ~spl2_1 | ~spl2_4 | spl2_34),
% 0.21/0.53    inference(avatar_split_clause,[],[f272,f265,f60,f45])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    spl2_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.53  fof(f265,plain,(
% 0.21/0.53    spl2_34 <=> r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.21/0.53  fof(f272,plain,(
% 0.21/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_34),
% 0.21/0.53    inference(resolution,[],[f267,f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_tops_1)).
% 0.21/0.53  fof(f267,plain,(
% 0.21/0.53    ~r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) | spl2_34),
% 0.21/0.53    inference(avatar_component_clause,[],[f265])).
% 0.21/0.53  fof(f269,plain,(
% 0.21/0.53    spl2_33 | ~spl2_34 | ~spl2_28),
% 0.21/0.53    inference(avatar_split_clause,[],[f259,f220,f265,f261])).
% 0.21/0.53  fof(f220,plain,(
% 0.21/0.53    spl2_28 <=> r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.21/0.53  fof(f259,plain,(
% 0.21/0.53    ~r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) | k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k1_tops_1(sK0,sK1)) | ~spl2_28),
% 0.21/0.53    inference(resolution,[],[f222,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f222,plain,(
% 0.21/0.53    r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) | ~spl2_28),
% 0.21/0.53    inference(avatar_component_clause,[],[f220])).
% 0.21/0.53  fof(f227,plain,(
% 0.21/0.53    ~spl2_1 | ~spl2_4 | spl2_27),
% 0.21/0.53    inference(avatar_split_clause,[],[f225,f216,f60,f45])).
% 0.21/0.53  fof(f225,plain,(
% 0.21/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_27),
% 0.21/0.53    inference(resolution,[],[f218,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 0.21/0.53  fof(f218,plain,(
% 0.21/0.53    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_27),
% 0.21/0.53    inference(avatar_component_clause,[],[f216])).
% 0.21/0.53  fof(f223,plain,(
% 0.21/0.53    ~spl2_1 | ~spl2_27 | spl2_28 | ~spl2_25),
% 0.21/0.53    inference(avatar_split_clause,[],[f213,f202,f220,f216,f45])).
% 0.21/0.53  fof(f213,plain,(
% 0.21/0.53    r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_25),
% 0.21/0.53    inference(superposition,[],[f30,f204])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tops_1)).
% 0.21/0.53  fof(f211,plain,(
% 0.21/0.53    ~spl2_26 | spl2_2 | ~spl2_25),
% 0.21/0.53    inference(avatar_split_clause,[],[f206,f202,f50,f208])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    spl2_2 <=> r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.53  fof(f206,plain,(
% 0.21/0.53    ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | (spl2_2 | ~spl2_25)),
% 0.21/0.53    inference(backward_demodulation,[],[f52,f204])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) | spl2_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f50])).
% 0.21/0.53  fof(f205,plain,(
% 0.21/0.53    ~spl2_4 | spl2_25 | ~spl2_1 | ~spl2_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f200,f55,f45,f202,f60])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    spl2_3 <=> v5_tops_1(sK1,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.53  fof(f200,plain,(
% 0.21/0.53    sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_1 | ~spl2_3)),
% 0.21/0.53    inference(resolution,[],[f199,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    v5_tops_1(sK1,sK0) | ~spl2_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f55])).
% 0.21/0.53  fof(f199,plain,(
% 0.21/0.53    ( ! [X0] : (~v5_tops_1(X0,sK0) | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_1),
% 0.21/0.53    inference(resolution,[],[f33,f47])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    spl2_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f25,f60])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,negated_conjecture,(
% 0.21/0.53    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f11])).
% 0.21/0.53  fof(f11,conjecture,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tops_1)).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    spl2_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f26,f55])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    v5_tops_1(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ~spl2_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f27,f50])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    spl2_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f28,f45])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    l1_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (683)------------------------------
% 0.21/0.53  % (683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (683)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (683)Memory used [KB]: 6524
% 0.21/0.53  % (683)Time elapsed: 0.126 s
% 0.21/0.53  % (683)------------------------------
% 0.21/0.53  % (683)------------------------------
% 0.21/0.53  % (686)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (667)Success in time 0.174 s
%------------------------------------------------------------------------------
