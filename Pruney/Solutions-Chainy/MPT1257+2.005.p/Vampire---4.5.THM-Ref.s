%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:28 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 181 expanded)
%              Number of leaves         :   27 (  88 expanded)
%              Depth                    :    6
%              Number of atoms          :  264 ( 448 expanded)
%              Number of equality atoms :   29 (  42 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f833,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f56,f61,f67,f73,f112,f292,f335,f342,f354,f360,f384,f394,f416,f617,f802])).

fof(f802,plain,
    ( ~ spl2_55
    | spl2_1
    | ~ spl2_5
    | ~ spl2_87 ),
    inference(avatar_split_clause,[],[f683,f614,f70,f48,f413])).

fof(f413,plain,
    ( spl2_55
  <=> r1_tarski(k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).

fof(f48,plain,
    ( spl2_1
  <=> r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f70,plain,
    ( spl2_5
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f614,plain,
    ( spl2_87
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_87])])).

fof(f683,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | spl2_1
    | ~ spl2_5
    | ~ spl2_87 ),
    inference(unit_resulting_resolution,[],[f50,f72,f616,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,X2)
              | ~ r1_tarski(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

fof(f616,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_87 ),
    inference(avatar_component_clause,[],[f614])).

fof(f72,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f50,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f617,plain,
    ( ~ spl2_43
    | spl2_87
    | ~ spl2_51 ),
    inference(avatar_split_clause,[],[f592,f391,f614,f339])).

fof(f339,plain,
    ( spl2_43
  <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f391,plain,
    ( spl2_51
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).

fof(f592,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_51 ),
    inference(superposition,[],[f46,f393])).

fof(f393,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_51 ),
    inference(avatar_component_clause,[],[f391])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f416,plain,
    ( spl2_55
    | ~ spl2_50
    | ~ spl2_51 ),
    inference(avatar_split_clause,[],[f410,f391,f381,f413])).

fof(f381,plain,
    ( spl2_50
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).

fof(f410,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl2_50
    | ~ spl2_51 ),
    inference(backward_demodulation,[],[f383,f393])).

fof(f383,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl2_50 ),
    inference(avatar_component_clause,[],[f381])).

fof(f394,plain,
    ( spl2_51
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f388,f58,f53,f391])).

fof(f53,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f58,plain,
    ( spl2_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f388,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f60,f55,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f55,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f60,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f384,plain,
    ( spl2_50
    | ~ spl2_34
    | ~ spl2_46 ),
    inference(avatar_split_clause,[],[f379,f356,f289,f381])).

fof(f289,plain,
    ( spl2_34
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f356,plain,
    ( spl2_46
  <=> k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f379,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl2_34
    | ~ spl2_46 ),
    inference(backward_demodulation,[],[f291,f358])).

fof(f358,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_46 ),
    inference(avatar_component_clause,[],[f356])).

fof(f291,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f289])).

fof(f360,plain,
    ( spl2_46
    | ~ spl2_41
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f359,f351,f325,f356])).

fof(f325,plain,
    ( spl2_41
  <=> k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f351,plain,
    ( spl2_45
  <=> k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f359,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_41
    | ~ spl2_45 ),
    inference(forward_demodulation,[],[f327,f353])).

fof(f353,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f351])).

fof(f327,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_41 ),
    inference(avatar_component_clause,[],[f325])).

fof(f354,plain,
    ( spl2_45
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f349,f109,f64,f58,f351])).

fof(f64,plain,
    ( spl2_4
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f109,plain,
    ( spl2_11
  <=> k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f349,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f257,f111])).

fof(f111,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f109])).

fof(f257,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f60,f66,f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f66,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f342,plain,
    ( spl2_43
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f259,f64,f58,f339])).

fof(f259,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f60,f66,f42])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f335,plain,
    ( spl2_41
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f263,f70,f64,f325])).

fof(f263,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f72,f66,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

fof(f292,plain,
    ( spl2_34
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f275,f70,f64,f289])).

fof(f275,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f72,f66,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

fof(f112,plain,
    ( spl2_11
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f100,f58,f53,f109])).

fof(f100,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f60,f55,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

fof(f73,plain,
    ( spl2_5
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f68,f58,f53,f70])).

fof(f68,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f60,f55,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f67,plain,
    ( spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f62,f53,f64])).

fof(f62,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f55,f46])).

fof(f61,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f32,f58])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_xboole_0(k1_tops_1(sK0,X1),k2_tops_1(sK0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ~ r1_xboole_0(k1_tops_1(sK0,X1),k2_tops_1(sK0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tops_1)).

fof(f56,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f33,f53])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f34,f48])).

fof(f34,plain,(
    ~ r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:24:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.45  % (19615)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.46  % (19626)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.49  % (19625)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.50  % (19634)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.51  % (19618)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.51  % (19620)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.51  % (19618)Refutation not found, incomplete strategy% (19618)------------------------------
% 0.22/0.51  % (19618)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (19618)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (19618)Memory used [KB]: 10490
% 0.22/0.51  % (19618)Time elapsed: 0.103 s
% 0.22/0.51  % (19618)------------------------------
% 0.22/0.51  % (19618)------------------------------
% 0.22/0.51  % (19637)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.51  % (19625)Refutation not found, incomplete strategy% (19625)------------------------------
% 0.22/0.51  % (19625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (19624)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.51  % (19636)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.51  % (19625)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (19625)Memory used [KB]: 10618
% 0.22/0.51  % (19625)Time elapsed: 0.102 s
% 0.22/0.51  % (19625)------------------------------
% 0.22/0.51  % (19625)------------------------------
% 0.22/0.51  % (19621)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.51  % (19632)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.52  % (19631)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.52  % (19622)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (19633)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.52  % (19616)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.52  % (19628)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.52  % (19629)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.52  % (19638)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.52  % (19638)Refutation not found, incomplete strategy% (19638)------------------------------
% 0.22/0.52  % (19638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (19638)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (19638)Memory used [KB]: 10618
% 0.22/0.52  % (19638)Time elapsed: 0.115 s
% 0.22/0.52  % (19638)------------------------------
% 0.22/0.52  % (19638)------------------------------
% 0.22/0.52  % (19623)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.52  % (19635)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.52  % (19619)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.53  % (19617)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.54  % (19630)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.45/0.54  % (19627)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 1.45/0.54  % (19621)Refutation found. Thanks to Tanya!
% 1.45/0.54  % SZS status Theorem for theBenchmark
% 1.45/0.54  % SZS output start Proof for theBenchmark
% 1.45/0.54  fof(f833,plain,(
% 1.45/0.54    $false),
% 1.45/0.54    inference(avatar_sat_refutation,[],[f51,f56,f61,f67,f73,f112,f292,f335,f342,f354,f360,f384,f394,f416,f617,f802])).
% 1.45/0.54  fof(f802,plain,(
% 1.45/0.54    ~spl2_55 | spl2_1 | ~spl2_5 | ~spl2_87),
% 1.45/0.54    inference(avatar_split_clause,[],[f683,f614,f70,f48,f413])).
% 1.45/0.54  fof(f413,plain,(
% 1.45/0.54    spl2_55 <=> r1_tarski(k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).
% 1.45/0.54  fof(f48,plain,(
% 1.45/0.54    spl2_1 <=> r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.45/0.54  fof(f70,plain,(
% 1.45/0.54    spl2_5 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.45/0.54  fof(f614,plain,(
% 1.45/0.54    spl2_87 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_87])])).
% 1.45/0.54  fof(f683,plain,(
% 1.45/0.54    ~r1_tarski(k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | (spl2_1 | ~spl2_5 | ~spl2_87)),
% 1.45/0.54    inference(unit_resulting_resolution,[],[f50,f72,f616,f36])).
% 1.45/0.54  fof(f36,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.45/0.54    inference(cnf_transformation,[],[f30])).
% 1.45/0.54  fof(f30,plain,(
% 1.45/0.54    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,X2) | ~r1_tarski(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.45/0.54    inference(nnf_transformation,[],[f14])).
% 1.45/0.54  fof(f14,plain,(
% 1.45/0.54    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.45/0.54    inference(ennf_transformation,[],[f5])).
% 1.45/0.54  fof(f5,axiom,(
% 1.45/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 1.45/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).
% 1.45/0.54  fof(f616,plain,(
% 1.45/0.54    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_87),
% 1.45/0.54    inference(avatar_component_clause,[],[f614])).
% 1.45/0.54  fof(f72,plain,(
% 1.45/0.54    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_5),
% 1.45/0.54    inference(avatar_component_clause,[],[f70])).
% 1.45/0.54  fof(f50,plain,(
% 1.45/0.54    ~r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | spl2_1),
% 1.45/0.54    inference(avatar_component_clause,[],[f48])).
% 1.45/0.54  fof(f617,plain,(
% 1.45/0.54    ~spl2_43 | spl2_87 | ~spl2_51),
% 1.45/0.54    inference(avatar_split_clause,[],[f592,f391,f614,f339])).
% 1.45/0.54  fof(f339,plain,(
% 1.45/0.54    spl2_43 <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 1.45/0.54  fof(f391,plain,(
% 1.45/0.54    spl2_51 <=> k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).
% 1.45/0.54  fof(f592,plain,(
% 1.45/0.54    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_51),
% 1.45/0.54    inference(superposition,[],[f46,f393])).
% 1.45/0.54  fof(f393,plain,(
% 1.45/0.54    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~spl2_51),
% 1.45/0.54    inference(avatar_component_clause,[],[f391])).
% 1.45/0.54  fof(f46,plain,(
% 1.45/0.54    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.45/0.54    inference(cnf_transformation,[],[f26])).
% 1.45/0.54  fof(f26,plain,(
% 1.45/0.54    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.45/0.54    inference(ennf_transformation,[],[f2])).
% 1.45/0.54  fof(f2,axiom,(
% 1.45/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.45/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.45/0.54  fof(f416,plain,(
% 1.45/0.54    spl2_55 | ~spl2_50 | ~spl2_51),
% 1.45/0.54    inference(avatar_split_clause,[],[f410,f391,f381,f413])).
% 1.45/0.54  fof(f381,plain,(
% 1.45/0.54    spl2_50 <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).
% 1.45/0.54  fof(f410,plain,(
% 1.45/0.54    r1_tarski(k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | (~spl2_50 | ~spl2_51)),
% 1.45/0.54    inference(backward_demodulation,[],[f383,f393])).
% 1.45/0.54  fof(f383,plain,(
% 1.45/0.54    r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | ~spl2_50),
% 1.45/0.54    inference(avatar_component_clause,[],[f381])).
% 1.45/0.54  fof(f394,plain,(
% 1.45/0.54    spl2_51 | ~spl2_2 | ~spl2_3),
% 1.45/0.54    inference(avatar_split_clause,[],[f388,f58,f53,f391])).
% 1.45/0.54  fof(f53,plain,(
% 1.45/0.54    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.45/0.54  fof(f58,plain,(
% 1.45/0.54    spl2_3 <=> l1_pre_topc(sK0)),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.45/0.54  fof(f388,plain,(
% 1.45/0.54    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl2_2 | ~spl2_3)),
% 1.45/0.54    inference(unit_resulting_resolution,[],[f60,f55,f40])).
% 1.45/0.54  fof(f40,plain,(
% 1.45/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 1.45/0.54    inference(cnf_transformation,[],[f19])).
% 1.45/0.54  fof(f19,plain,(
% 1.45/0.54    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.45/0.54    inference(ennf_transformation,[],[f7])).
% 1.45/0.54  fof(f7,axiom,(
% 1.45/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 1.45/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 1.45/0.54  fof(f55,plain,(
% 1.45/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 1.45/0.54    inference(avatar_component_clause,[],[f53])).
% 1.45/0.54  fof(f60,plain,(
% 1.45/0.54    l1_pre_topc(sK0) | ~spl2_3),
% 1.45/0.54    inference(avatar_component_clause,[],[f58])).
% 1.45/0.54  fof(f384,plain,(
% 1.45/0.54    spl2_50 | ~spl2_34 | ~spl2_46),
% 1.45/0.54    inference(avatar_split_clause,[],[f379,f356,f289,f381])).
% 1.45/0.54  fof(f289,plain,(
% 1.45/0.54    spl2_34 <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 1.45/0.54  fof(f356,plain,(
% 1.45/0.54    spl2_46 <=> k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 1.45/0.54  fof(f379,plain,(
% 1.45/0.54    r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | (~spl2_34 | ~spl2_46)),
% 1.45/0.54    inference(backward_demodulation,[],[f291,f358])).
% 1.45/0.54  fof(f358,plain,(
% 1.45/0.54    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_46),
% 1.45/0.54    inference(avatar_component_clause,[],[f356])).
% 1.45/0.54  fof(f291,plain,(
% 1.45/0.54    r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | ~spl2_34),
% 1.45/0.54    inference(avatar_component_clause,[],[f289])).
% 1.45/0.54  fof(f360,plain,(
% 1.45/0.54    spl2_46 | ~spl2_41 | ~spl2_45),
% 1.45/0.54    inference(avatar_split_clause,[],[f359,f351,f325,f356])).
% 1.45/0.54  fof(f325,plain,(
% 1.45/0.54    spl2_41 <=> k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 1.45/0.54  fof(f351,plain,(
% 1.45/0.54    spl2_45 <=> k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 1.45/0.54  fof(f359,plain,(
% 1.45/0.54    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_41 | ~spl2_45)),
% 1.45/0.54    inference(forward_demodulation,[],[f327,f353])).
% 1.45/0.54  fof(f353,plain,(
% 1.45/0.54    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) | ~spl2_45),
% 1.45/0.54    inference(avatar_component_clause,[],[f351])).
% 1.45/0.54  fof(f327,plain,(
% 1.45/0.54    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_41),
% 1.45/0.54    inference(avatar_component_clause,[],[f325])).
% 1.45/0.54  fof(f354,plain,(
% 1.45/0.54    spl2_45 | ~spl2_3 | ~spl2_4 | ~spl2_11),
% 1.45/0.54    inference(avatar_split_clause,[],[f349,f109,f64,f58,f351])).
% 1.45/0.54  fof(f64,plain,(
% 1.45/0.54    spl2_4 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.45/0.54  fof(f109,plain,(
% 1.45/0.54    spl2_11 <=> k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.45/0.54  fof(f349,plain,(
% 1.45/0.54    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_4 | ~spl2_11)),
% 1.45/0.54    inference(forward_demodulation,[],[f257,f111])).
% 1.45/0.54  fof(f111,plain,(
% 1.45/0.54    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_11),
% 1.45/0.54    inference(avatar_component_clause,[],[f109])).
% 1.45/0.54  fof(f257,plain,(
% 1.45/0.54    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl2_3 | ~spl2_4)),
% 1.45/0.54    inference(unit_resulting_resolution,[],[f60,f66,f38])).
% 1.45/0.54  fof(f38,plain,(
% 1.45/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 1.45/0.54    inference(cnf_transformation,[],[f17])).
% 1.45/0.54  fof(f17,plain,(
% 1.45/0.54    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.45/0.54    inference(ennf_transformation,[],[f10])).
% 1.45/0.54  fof(f10,axiom,(
% 1.45/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.45/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 1.45/0.54  fof(f66,plain,(
% 1.45/0.54    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_4),
% 1.45/0.54    inference(avatar_component_clause,[],[f64])).
% 1.45/0.54  fof(f342,plain,(
% 1.45/0.54    spl2_43 | ~spl2_3 | ~spl2_4),
% 1.45/0.54    inference(avatar_split_clause,[],[f259,f64,f58,f339])).
% 1.45/0.54  fof(f259,plain,(
% 1.45/0.54    m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_3 | ~spl2_4)),
% 1.45/0.54    inference(unit_resulting_resolution,[],[f60,f66,f42])).
% 1.45/0.54  fof(f42,plain,(
% 1.45/0.54    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f23])).
% 1.45/0.54  fof(f23,plain,(
% 1.45/0.54    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.45/0.54    inference(flattening,[],[f22])).
% 1.45/0.54  fof(f22,plain,(
% 1.45/0.54    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.45/0.54    inference(ennf_transformation,[],[f6])).
% 1.45/0.54  fof(f6,axiom,(
% 1.45/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.45/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 1.45/0.54  fof(f335,plain,(
% 1.45/0.54    spl2_41 | ~spl2_4 | ~spl2_5),
% 1.45/0.54    inference(avatar_split_clause,[],[f263,f70,f64,f325])).
% 1.45/0.54  fof(f263,plain,(
% 1.45/0.54    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_4 | ~spl2_5)),
% 1.45/0.54    inference(unit_resulting_resolution,[],[f72,f66,f41])).
% 1.45/0.54  fof(f41,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.45/0.54    inference(cnf_transformation,[],[f21])).
% 1.45/0.54  fof(f21,plain,(
% 1.45/0.54    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.45/0.54    inference(flattening,[],[f20])).
% 1.45/0.54  fof(f20,plain,(
% 1.45/0.54    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.45/0.54    inference(ennf_transformation,[],[f1])).
% 1.45/0.54  fof(f1,axiom,(
% 1.45/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1))),
% 1.45/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).
% 1.45/0.54  fof(f292,plain,(
% 1.45/0.54    spl2_34 | ~spl2_4 | ~spl2_5),
% 1.45/0.54    inference(avatar_split_clause,[],[f275,f70,f64,f289])).
% 1.45/0.54  fof(f275,plain,(
% 1.45/0.54    r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | (~spl2_4 | ~spl2_5)),
% 1.45/0.54    inference(unit_resulting_resolution,[],[f72,f66,f45])).
% 1.45/0.54  fof(f45,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.45/0.54    inference(cnf_transformation,[],[f25])).
% 1.45/0.54  fof(f25,plain,(
% 1.45/0.54    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.45/0.54    inference(ennf_transformation,[],[f4])).
% 1.45/0.54  fof(f4,axiom,(
% 1.45/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 1.45/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).
% 1.45/0.54  fof(f112,plain,(
% 1.45/0.54    spl2_11 | ~spl2_2 | ~spl2_3),
% 1.45/0.54    inference(avatar_split_clause,[],[f100,f58,f53,f109])).
% 1.45/0.54  fof(f100,plain,(
% 1.45/0.54    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_2 | ~spl2_3)),
% 1.45/0.54    inference(unit_resulting_resolution,[],[f60,f55,f39])).
% 1.45/0.54  fof(f39,plain,(
% 1.45/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))) )),
% 1.45/0.54    inference(cnf_transformation,[],[f18])).
% 1.45/0.54  fof(f18,plain,(
% 1.45/0.54    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.45/0.54    inference(ennf_transformation,[],[f9])).
% 1.45/0.54  fof(f9,axiom,(
% 1.45/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 1.45/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).
% 1.45/0.54  fof(f73,plain,(
% 1.45/0.54    spl2_5 | ~spl2_2 | ~spl2_3),
% 1.45/0.54    inference(avatar_split_clause,[],[f68,f58,f53,f70])).
% 1.45/0.54  fof(f68,plain,(
% 1.45/0.54    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_3)),
% 1.45/0.54    inference(unit_resulting_resolution,[],[f60,f55,f37])).
% 1.45/0.54  fof(f37,plain,(
% 1.45/0.54    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f16])).
% 1.45/0.54  fof(f16,plain,(
% 1.45/0.54    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.45/0.54    inference(flattening,[],[f15])).
% 1.45/0.54  fof(f15,plain,(
% 1.45/0.54    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.45/0.54    inference(ennf_transformation,[],[f8])).
% 1.45/0.54  fof(f8,axiom,(
% 1.45/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.45/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 1.45/0.54  fof(f67,plain,(
% 1.45/0.54    spl2_4 | ~spl2_2),
% 1.45/0.54    inference(avatar_split_clause,[],[f62,f53,f64])).
% 1.45/0.54  fof(f62,plain,(
% 1.45/0.54    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 1.45/0.54    inference(unit_resulting_resolution,[],[f55,f46])).
% 1.45/0.54  fof(f61,plain,(
% 1.45/0.54    spl2_3),
% 1.45/0.54    inference(avatar_split_clause,[],[f32,f58])).
% 1.45/0.54  fof(f32,plain,(
% 1.45/0.54    l1_pre_topc(sK0)),
% 1.45/0.54    inference(cnf_transformation,[],[f29])).
% 1.45/0.54  fof(f29,plain,(
% 1.45/0.54    (~r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.45/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f28,f27])).
% 1.45/0.54  fof(f27,plain,(
% 1.45/0.54    ? [X0] : (? [X1] : (~r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_xboole_0(k1_tops_1(sK0,X1),k2_tops_1(sK0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.45/0.54    introduced(choice_axiom,[])).
% 1.45/0.54  fof(f28,plain,(
% 1.45/0.54    ? [X1] : (~r1_xboole_0(k1_tops_1(sK0,X1),k2_tops_1(sK0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.45/0.54    introduced(choice_axiom,[])).
% 1.45/0.54  fof(f13,plain,(
% 1.45/0.54    ? [X0] : (? [X1] : (~r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.45/0.54    inference(ennf_transformation,[],[f12])).
% 1.45/0.54  fof(f12,negated_conjecture,(
% 1.45/0.54    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))))),
% 1.45/0.54    inference(negated_conjecture,[],[f11])).
% 1.45/0.54  fof(f11,conjecture,(
% 1.45/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))))),
% 1.45/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tops_1)).
% 1.45/0.54  fof(f56,plain,(
% 1.45/0.54    spl2_2),
% 1.45/0.54    inference(avatar_split_clause,[],[f33,f53])).
% 1.45/0.54  fof(f33,plain,(
% 1.45/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.45/0.54    inference(cnf_transformation,[],[f29])).
% 1.45/0.54  fof(f51,plain,(
% 1.45/0.54    ~spl2_1),
% 1.45/0.54    inference(avatar_split_clause,[],[f34,f48])).
% 1.45/0.54  fof(f34,plain,(
% 1.45/0.54    ~r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 1.45/0.54    inference(cnf_transformation,[],[f29])).
% 1.45/0.54  % SZS output end Proof for theBenchmark
% 1.45/0.54  % (19621)------------------------------
% 1.45/0.54  % (19621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.54  % (19621)Termination reason: Refutation
% 1.45/0.54  
% 1.45/0.54  % (19621)Memory used [KB]: 11257
% 1.45/0.54  % (19621)Time elapsed: 0.072 s
% 1.45/0.54  % (19621)------------------------------
% 1.45/0.54  % (19621)------------------------------
% 1.45/0.54  % (19614)Success in time 0.182 s
%------------------------------------------------------------------------------
