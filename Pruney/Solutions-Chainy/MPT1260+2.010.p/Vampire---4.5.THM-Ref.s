%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:34 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 243 expanded)
%              Number of leaves         :   15 (  57 expanded)
%              Depth                    :   13
%              Number of atoms          :  227 ( 785 expanded)
%              Number of equality atoms :   36 ( 148 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1061,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f165,f774,f977,f1054,f1060])).

fof(f1060,plain,
    ( ~ spl5_1
    | spl5_8 ),
    inference(avatar_contradiction_clause,[],[f1057])).

fof(f1057,plain,
    ( $false
    | ~ spl5_1
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f160,f782])).

fof(f782,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f94,f773,f55,f55,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k1_tops_1(sK0,X1)) ) ),
    inference(resolution,[],[f57,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f31])).

fof(f31,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(f55,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f773,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f771])).

fof(f771,plain,
    ( spl5_8
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f94,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f160,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl5_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1054,plain,(
    ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f1051])).

fof(f1051,plain,
    ( $false
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f983,f1050])).

fof(f1050,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl5_7 ),
    inference(trivial_inequality_removal,[],[f1049])).

fof(f1049,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f151,f1028])).

fof(f1028,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f942,f769])).

fof(f769,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f767])).

fof(f767,plain,
    ( spl5_7
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f942,plain,(
    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f143,f107])).

fof(f107,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f57,f55,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f143,plain,(
    ! [X0] : k4_xboole_0(k2_pre_topc(sK0,sK1),X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) ),
    inference(unit_resulting_resolution,[],[f109,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f109,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f57,f55,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f151,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f54,f143])).

fof(f54,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f983,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f111,f769])).

fof(f111,plain,(
    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f57,f56,f55,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f56,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f977,plain,
    ( ~ spl5_2
    | spl5_8 ),
    inference(avatar_contradiction_clause,[],[f956])).

fof(f956,plain,
    ( $false
    | ~ spl5_2
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f94,f778,f826,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f826,plain,
    ( r2_hidden(sK2(sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ spl5_2
    | spl5_8 ),
    inference(forward_demodulation,[],[f814,f371])).

fof(f371,plain,(
    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f108,f116])).

fof(f116,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(unit_resulting_resolution,[],[f55,f58])).

fof(f108,plain,(
    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f57,f55,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f814,plain,
    ( r2_hidden(sK2(sK1,k1_tops_1(sK0,sK1)),k4_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl5_2
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f777,f775,f95])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f775,plain,
    ( ~ r2_hidden(sK2(sK1,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | ~ spl5_2
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f773,f209])).

fof(f209,plain,
    ( ! [X8] :
        ( r1_tarski(sK1,X8)
        | ~ r2_hidden(sK2(sK1,X8),k2_tops_1(sK0,sK1)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f198,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f198,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,k2_tops_1(sK0,sK1)) )
    | ~ spl5_2 ),
    inference(superposition,[],[f96,f164])).

fof(f164,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl5_2
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f777,plain,
    ( r2_hidden(sK2(sK1,k1_tops_1(sK0,sK1)),sK1)
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f773,f72])).

fof(f778,plain,
    ( ~ r2_hidden(sK2(sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f773,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f774,plain,
    ( spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f385,f771,f767])).

fof(f385,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f379,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f379,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[],[f65,f371])).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f165,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f150,f162,f158])).

fof(f150,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f53,f143])).

fof(f53,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:34:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.46  % (8960)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.50  % (8968)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.50  % (8975)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (8961)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (8969)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.22/0.52  % (8957)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.22/0.52  % (8958)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.22/0.52  % (8976)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.22/0.53  % (8959)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.22/0.53  % (8984)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.22/0.53  % (8962)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.22/0.53  % (8979)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.22/0.53  % (8971)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.22/0.53  % (8980)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.22/0.53  % (8963)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.22/0.54  % (8985)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.22/0.54  % (8973)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.22/0.54  % (8983)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.41/0.54  % (8972)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.41/0.54  % (8986)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.41/0.54  % (8966)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.41/0.55  % (8978)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.41/0.55  % (8964)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.41/0.55  % (8974)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.41/0.55  % (8970)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.41/0.55  % (8974)Refutation not found, incomplete strategy% (8974)------------------------------
% 1.41/0.55  % (8974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (8974)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (8974)Memory used [KB]: 10746
% 1.41/0.55  % (8974)Time elapsed: 0.135 s
% 1.41/0.55  % (8974)------------------------------
% 1.41/0.55  % (8974)------------------------------
% 1.41/0.55  % (8977)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.55  % (8967)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.41/0.55  % (8965)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.41/0.56  % (8981)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.41/0.56  % (8982)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.41/0.56  % (8961)Refutation found. Thanks to Tanya!
% 1.41/0.56  % SZS status Theorem for theBenchmark
% 1.41/0.57  % SZS output start Proof for theBenchmark
% 1.41/0.57  fof(f1061,plain,(
% 1.41/0.57    $false),
% 1.41/0.57    inference(avatar_sat_refutation,[],[f165,f774,f977,f1054,f1060])).
% 1.41/0.57  fof(f1060,plain,(
% 1.41/0.57    ~spl5_1 | spl5_8),
% 1.41/0.57    inference(avatar_contradiction_clause,[],[f1057])).
% 1.41/0.57  fof(f1057,plain,(
% 1.41/0.57    $false | (~spl5_1 | spl5_8)),
% 1.41/0.57    inference(unit_resulting_resolution,[],[f160,f782])).
% 1.41/0.57  fof(f782,plain,(
% 1.41/0.57    ~v3_pre_topc(sK1,sK0) | spl5_8),
% 1.41/0.57    inference(unit_resulting_resolution,[],[f94,f773,f55,f55,f102])).
% 1.41/0.57  fof(f102,plain,(
% 1.41/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~r1_tarski(X0,X1) | r1_tarski(X0,k1_tops_1(sK0,X1))) )),
% 1.41/0.57    inference(resolution,[],[f57,f64])).
% 1.41/0.57  fof(f64,plain,(
% 1.41/0.57    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~r1_tarski(X1,X2) | r1_tarski(X1,k1_tops_1(X0,X2))) )),
% 1.41/0.57    inference(cnf_transformation,[],[f45])).
% 1.41/0.57  fof(f45,plain,(
% 1.41/0.57    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.41/0.57    inference(flattening,[],[f44])).
% 1.41/0.57  fof(f44,plain,(
% 1.41/0.57    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.41/0.57    inference(ennf_transformation,[],[f28])).
% 1.41/0.57  fof(f28,axiom,(
% 1.41/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 1.41/0.57  fof(f57,plain,(
% 1.41/0.57    l1_pre_topc(sK0)),
% 1.41/0.57    inference(cnf_transformation,[],[f35])).
% 1.41/0.57  fof(f35,plain,(
% 1.41/0.57    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.41/0.57    inference(flattening,[],[f34])).
% 1.41/0.57  fof(f34,plain,(
% 1.41/0.57    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.41/0.57    inference(ennf_transformation,[],[f32])).
% 1.41/0.57  fof(f32,negated_conjecture,(
% 1.41/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 1.41/0.57    inference(negated_conjecture,[],[f31])).
% 1.41/0.57  fof(f31,conjecture,(
% 1.41/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).
% 1.41/0.57  fof(f55,plain,(
% 1.41/0.57    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.41/0.57    inference(cnf_transformation,[],[f35])).
% 1.41/0.57  fof(f773,plain,(
% 1.41/0.57    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | spl5_8),
% 1.41/0.57    inference(avatar_component_clause,[],[f771])).
% 1.41/0.57  fof(f771,plain,(
% 1.41/0.57    spl5_8 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 1.41/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.41/0.57  fof(f94,plain,(
% 1.41/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.41/0.57    inference(equality_resolution,[],[f74])).
% 1.41/0.57  fof(f74,plain,(
% 1.41/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.41/0.57    inference(cnf_transformation,[],[f5])).
% 1.41/0.57  fof(f5,axiom,(
% 1.41/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.41/0.57  fof(f160,plain,(
% 1.41/0.57    v3_pre_topc(sK1,sK0) | ~spl5_1),
% 1.41/0.57    inference(avatar_component_clause,[],[f158])).
% 1.41/0.57  fof(f158,plain,(
% 1.41/0.57    spl5_1 <=> v3_pre_topc(sK1,sK0)),
% 1.41/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.41/0.57  fof(f1054,plain,(
% 1.41/0.57    ~spl5_7),
% 1.41/0.57    inference(avatar_contradiction_clause,[],[f1051])).
% 1.41/0.57  fof(f1051,plain,(
% 1.41/0.57    $false | ~spl5_7),
% 1.41/0.57    inference(unit_resulting_resolution,[],[f983,f1050])).
% 1.41/0.57  fof(f1050,plain,(
% 1.41/0.57    ~v3_pre_topc(sK1,sK0) | ~spl5_7),
% 1.41/0.57    inference(trivial_inequality_removal,[],[f1049])).
% 1.41/0.57  fof(f1049,plain,(
% 1.41/0.57    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | ~spl5_7),
% 1.41/0.57    inference(forward_demodulation,[],[f151,f1028])).
% 1.41/0.57  fof(f1028,plain,(
% 1.41/0.57    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl5_7),
% 1.41/0.57    inference(backward_demodulation,[],[f942,f769])).
% 1.41/0.57  fof(f769,plain,(
% 1.41/0.57    sK1 = k1_tops_1(sK0,sK1) | ~spl5_7),
% 1.41/0.57    inference(avatar_component_clause,[],[f767])).
% 1.41/0.57  fof(f767,plain,(
% 1.41/0.57    spl5_7 <=> sK1 = k1_tops_1(sK0,sK1)),
% 1.41/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.41/0.57  fof(f942,plain,(
% 1.41/0.57    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 1.41/0.57    inference(superposition,[],[f143,f107])).
% 1.41/0.57  fof(f107,plain,(
% 1.41/0.57    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 1.41/0.57    inference(unit_resulting_resolution,[],[f57,f55,f59])).
% 1.41/0.57  fof(f59,plain,(
% 1.41/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 1.41/0.57    inference(cnf_transformation,[],[f37])).
% 1.41/0.57  fof(f37,plain,(
% 1.41/0.57    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.41/0.57    inference(ennf_transformation,[],[f27])).
% 1.41/0.57  fof(f27,axiom,(
% 1.41/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 1.41/0.57  fof(f143,plain,(
% 1.41/0.57    ( ! [X0] : (k4_xboole_0(k2_pre_topc(sK0,sK1),X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0)) )),
% 1.41/0.57    inference(unit_resulting_resolution,[],[f109,f58])).
% 1.41/0.57  fof(f58,plain,(
% 1.41/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f36])).
% 1.41/0.57  fof(f36,plain,(
% 1.41/0.57    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.41/0.57    inference(ennf_transformation,[],[f20])).
% 1.41/0.57  fof(f20,axiom,(
% 1.41/0.57    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.41/0.57  fof(f109,plain,(
% 1.41/0.57    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.41/0.57    inference(unit_resulting_resolution,[],[f57,f55,f61])).
% 1.41/0.57  fof(f61,plain,(
% 1.41/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.41/0.57    inference(cnf_transformation,[],[f40])).
% 1.41/0.57  fof(f40,plain,(
% 1.41/0.57    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.41/0.57    inference(flattening,[],[f39])).
% 1.41/0.57  fof(f39,plain,(
% 1.41/0.57    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.41/0.57    inference(ennf_transformation,[],[f25])).
% 1.41/0.57  fof(f25,axiom,(
% 1.41/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 1.41/0.57  fof(f151,plain,(
% 1.41/0.57    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 1.41/0.57    inference(backward_demodulation,[],[f54,f143])).
% 1.41/0.57  fof(f54,plain,(
% 1.41/0.57    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 1.41/0.57    inference(cnf_transformation,[],[f35])).
% 1.41/0.57  fof(f983,plain,(
% 1.41/0.57    v3_pre_topc(sK1,sK0) | ~spl5_7),
% 1.41/0.57    inference(backward_demodulation,[],[f111,f769])).
% 1.41/0.57  fof(f111,plain,(
% 1.41/0.57    v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 1.41/0.57    inference(unit_resulting_resolution,[],[f57,f56,f55,f63])).
% 1.41/0.57  fof(f63,plain,(
% 1.41/0.57    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f43])).
% 1.41/0.57  fof(f43,plain,(
% 1.41/0.57    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.41/0.57    inference(flattening,[],[f42])).
% 1.41/0.57  fof(f42,plain,(
% 1.41/0.57    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.41/0.57    inference(ennf_transformation,[],[f26])).
% 1.41/0.57  fof(f26,axiom,(
% 1.41/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 1.41/0.57  fof(f56,plain,(
% 1.41/0.57    v2_pre_topc(sK0)),
% 1.41/0.57    inference(cnf_transformation,[],[f35])).
% 1.41/0.57  fof(f977,plain,(
% 1.41/0.57    ~spl5_2 | spl5_8),
% 1.41/0.57    inference(avatar_contradiction_clause,[],[f956])).
% 1.41/0.57  fof(f956,plain,(
% 1.41/0.57    $false | (~spl5_2 | spl5_8)),
% 1.41/0.57    inference(unit_resulting_resolution,[],[f94,f778,f826,f71])).
% 1.41/0.57  fof(f71,plain,(
% 1.41/0.57    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f49])).
% 1.41/0.57  fof(f49,plain,(
% 1.41/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.41/0.57    inference(ennf_transformation,[],[f1])).
% 1.41/0.57  fof(f1,axiom,(
% 1.41/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.41/0.57  fof(f826,plain,(
% 1.41/0.57    r2_hidden(sK2(sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | (~spl5_2 | spl5_8)),
% 1.41/0.57    inference(forward_demodulation,[],[f814,f371])).
% 1.41/0.57  fof(f371,plain,(
% 1.41/0.57    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 1.41/0.57    inference(superposition,[],[f108,f116])).
% 1.41/0.57  fof(f116,plain,(
% 1.41/0.57    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) )),
% 1.41/0.57    inference(unit_resulting_resolution,[],[f55,f58])).
% 1.41/0.57  fof(f108,plain,(
% 1.41/0.57    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 1.41/0.57    inference(unit_resulting_resolution,[],[f57,f55,f60])).
% 1.41/0.57  fof(f60,plain,(
% 1.41/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 1.41/0.57    inference(cnf_transformation,[],[f38])).
% 1.41/0.57  fof(f38,plain,(
% 1.41/0.57    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.41/0.57    inference(ennf_transformation,[],[f30])).
% 1.41/0.57  fof(f30,axiom,(
% 1.41/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 1.41/0.57  fof(f814,plain,(
% 1.41/0.57    r2_hidden(sK2(sK1,k1_tops_1(sK0,sK1)),k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) | (~spl5_2 | spl5_8)),
% 1.41/0.57    inference(unit_resulting_resolution,[],[f777,f775,f95])).
% 1.41/0.57  fof(f95,plain,(
% 1.41/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 1.41/0.57    inference(equality_resolution,[],[f83])).
% 1.41/0.57  fof(f83,plain,(
% 1.41/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.41/0.57    inference(cnf_transformation,[],[f3])).
% 1.41/0.57  fof(f3,axiom,(
% 1.41/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.41/0.57  fof(f775,plain,(
% 1.41/0.57    ~r2_hidden(sK2(sK1,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) | (~spl5_2 | spl5_8)),
% 1.41/0.57    inference(unit_resulting_resolution,[],[f773,f209])).
% 1.41/0.57  fof(f209,plain,(
% 1.41/0.57    ( ! [X8] : (r1_tarski(sK1,X8) | ~r2_hidden(sK2(sK1,X8),k2_tops_1(sK0,sK1))) ) | ~spl5_2),
% 1.41/0.57    inference(resolution,[],[f198,f72])).
% 1.41/0.57  fof(f72,plain,(
% 1.41/0.57    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f49])).
% 1.41/0.57  fof(f198,plain,(
% 1.41/0.57    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,k2_tops_1(sK0,sK1))) ) | ~spl5_2),
% 1.41/0.57    inference(superposition,[],[f96,f164])).
% 1.41/0.57  fof(f164,plain,(
% 1.41/0.57    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl5_2),
% 1.41/0.57    inference(avatar_component_clause,[],[f162])).
% 1.41/0.57  fof(f162,plain,(
% 1.41/0.57    spl5_2 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 1.41/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.41/0.57  fof(f96,plain,(
% 1.41/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 1.41/0.57    inference(equality_resolution,[],[f82])).
% 1.41/0.57  fof(f82,plain,(
% 1.41/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.41/0.57    inference(cnf_transformation,[],[f3])).
% 1.41/0.57  fof(f777,plain,(
% 1.41/0.57    r2_hidden(sK2(sK1,k1_tops_1(sK0,sK1)),sK1) | spl5_8),
% 1.41/0.57    inference(unit_resulting_resolution,[],[f773,f72])).
% 1.41/0.57  fof(f778,plain,(
% 1.41/0.57    ~r2_hidden(sK2(sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | spl5_8),
% 1.41/0.57    inference(unit_resulting_resolution,[],[f773,f73])).
% 1.41/0.57  fof(f73,plain,(
% 1.41/0.57    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f49])).
% 1.41/0.57  fof(f774,plain,(
% 1.41/0.57    spl5_7 | ~spl5_8),
% 1.41/0.57    inference(avatar_split_clause,[],[f385,f771,f767])).
% 1.41/0.57  fof(f385,plain,(
% 1.41/0.57    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | sK1 = k1_tops_1(sK0,sK1)),
% 1.41/0.57    inference(resolution,[],[f379,f76])).
% 1.41/0.57  fof(f76,plain,(
% 1.41/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.41/0.57    inference(cnf_transformation,[],[f5])).
% 1.41/0.57  fof(f379,plain,(
% 1.41/0.57    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.41/0.57    inference(superposition,[],[f65,f371])).
% 1.41/0.57  fof(f65,plain,(
% 1.41/0.57    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f8])).
% 1.41/0.57  fof(f8,axiom,(
% 1.41/0.57    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.41/0.57  fof(f165,plain,(
% 1.41/0.57    spl5_1 | spl5_2),
% 1.41/0.57    inference(avatar_split_clause,[],[f150,f162,f158])).
% 1.41/0.57  fof(f150,plain,(
% 1.41/0.57    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 1.41/0.57    inference(backward_demodulation,[],[f53,f143])).
% 1.41/0.57  fof(f53,plain,(
% 1.41/0.57    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 1.41/0.57    inference(cnf_transformation,[],[f35])).
% 1.41/0.57  % SZS output end Proof for theBenchmark
% 1.41/0.57  % (8961)------------------------------
% 1.41/0.57  % (8961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.57  % (8961)Termination reason: Refutation
% 1.41/0.57  
% 1.41/0.57  % (8961)Memory used [KB]: 6780
% 1.41/0.57  % (8961)Time elapsed: 0.135 s
% 1.41/0.57  % (8961)------------------------------
% 1.41/0.57  % (8961)------------------------------
% 1.41/0.57  % (8956)Success in time 0.215 s
%------------------------------------------------------------------------------
