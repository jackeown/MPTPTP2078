%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : pre_topc__t52_pre_topc.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:44 EDT 2019

% Result     : Theorem 7.66s
% Output     : Refutation 7.66s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 361 expanded)
%              Number of leaves         :   19 (  99 expanded)
%              Depth                    :   12
%              Number of atoms          :  334 (1683 expanded)
%              Number of equality atoms :   24 ( 329 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1242,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f135,f156,f161,f291,f444,f486,f1015,f1031,f1237])).

fof(f1237,plain,
    ( ~ spl8_0
    | spl8_3
    | ~ spl8_4
    | ~ spl8_28 ),
    inference(avatar_contradiction_clause,[],[f1225])).

fof(f1225,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_28 ),
    inference(unit_resulting_resolution,[],[f61,f112,f97,f313,f60,f60,f1195,f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X3,X0)
      | ~ r1_tarski(X1,X3)
      | r2_hidden(X3,sK3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2)
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2)
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ? [X2] :
              ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2)
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X3,X2)
                  <=> ( r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0) ) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t52_pre_topc.p',t46_pre_topc)).

fof(f1195,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_28 ),
    inference(forward_demodulation,[],[f1187,f310])).

fof(f310,plain,
    ( k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1)) = sK1
    | ~ spl8_0
    | ~ spl8_4 ),
    inference(forward_demodulation,[],[f302,f131])).

fof(f131,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl8_4
  <=> k2_pre_topc(sK0,sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f302,plain,
    ( k2_pre_topc(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1))
    | ~ spl8_0 ),
    inference(unit_resulting_resolution,[],[f61,f60,f112,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1187,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1)),sK0)
    | ~ spl8_0
    | ~ spl8_28 ),
    inference(unit_resulting_resolution,[],[f61,f112,f299,f1176,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v4_pre_topc(sK2(X0,X1),X0)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ? [X2] :
              ( ~ v4_pre_topc(X2,X0)
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ? [X2] :
              ( ~ v4_pre_topc(X2,X0)
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) )
           => v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t52_pre_topc.p',t44_pre_topc)).

fof(f1176,plain,
    ( v4_pre_topc(sK2(sK0,sK3(sK0,sK1)),sK0)
    | ~ spl8_0
    | ~ spl8_28 ),
    inference(unit_resulting_resolution,[],[f61,f112,f60,f1008,f1032,f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X3,X0)
      | ~ r2_hidden(X3,sK3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1032,plain,
    ( m1_subset_1(sK2(sK0,sK3(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_0
    | ~ spl8_28 ),
    inference(unit_resulting_resolution,[],[f299,f1008,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t52_pre_topc.p',t4_subset)).

fof(f1008,plain,
    ( r2_hidden(sK2(sK0,sK3(sK0,sK1)),sK3(sK0,sK1))
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f1007])).

fof(f1007,plain,
    ( spl8_28
  <=> r2_hidden(sK2(sK0,sK3(sK0,sK1)),sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f299,plain,
    ( m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl8_0 ),
    inference(unit_resulting_resolution,[],[f61,f60,f112,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f60,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ~ v4_pre_topc(X1,X0)
              & k2_pre_topc(X0,X1) = X1
              & v2_pre_topc(X0) )
            | ( k2_pre_topc(X0,X1) != X1
              & v4_pre_topc(X1,X0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ~ v4_pre_topc(X1,X0)
              & k2_pre_topc(X0,X1) = X1
              & v2_pre_topc(X0) )
            | ( k2_pre_topc(X0,X1) != X1
              & v4_pre_topc(X1,X0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( ( k2_pre_topc(X0,X1) = X1
                  & v2_pre_topc(X0) )
               => v4_pre_topc(X1,X0) )
              & ( v4_pre_topc(X1,X0)
               => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t52_pre_topc.p',t52_pre_topc)).

fof(f313,plain,
    ( ~ r2_hidden(sK1,sK3(sK0,sK1))
    | ~ spl8_0
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f61,f112,f60,f60,f115,f65])).

fof(f115,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl8_3
  <=> ~ v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f97,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t52_pre_topc.p',d10_xboole_0)).

fof(f112,plain,
    ( v2_pre_topc(sK0)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl8_0
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f61,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f1031,plain,
    ( ~ spl8_0
    | spl8_31 ),
    inference(avatar_contradiction_clause,[],[f1022])).

fof(f1022,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_31 ),
    inference(unit_resulting_resolution,[],[f322,f1014,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t52_pre_topc.p',t3_subset)).

fof(f1014,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f1013])).

fof(f1013,plain,
    ( spl8_31
  <=> ~ m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f322,plain,
    ( r1_tarski(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_0 ),
    inference(unit_resulting_resolution,[],[f299,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1015,plain,
    ( spl8_28
    | ~ spl8_31
    | spl8_2
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f510,f484,f130,f111,f117,f1013,f1007])).

fof(f117,plain,
    ( spl8_2
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f484,plain,
    ( spl8_18
  <=> ! [X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),X7),sK0)
        | r2_hidden(sK2(sK0,X7),X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f510,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r2_hidden(sK2(sK0,sK3(sK0,sK1)),sK3(sK0,sK1))
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_18 ),
    inference(superposition,[],[f485,f310])).

fof(f485,plain,
    ( ! [X7] :
        ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),X7),sK0)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | r2_hidden(sK2(sK0,X7),X7) )
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f484])).

fof(f486,plain,
    ( spl8_18
    | ~ spl8_13
    | ~ spl8_0 ),
    inference(avatar_split_clause,[],[f308,f111,f438,f484])).

fof(f438,plain,
    ( spl8_13
  <=> ~ l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f308,plain,
    ( ! [X7] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | r2_hidden(sK2(sK0,X7),X7)
        | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),X7),sK0) )
    | ~ spl8_0 ),
    inference(resolution,[],[f112,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r2_hidden(sK2(X0,X1),X1)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f444,plain,(
    spl8_13 ),
    inference(avatar_contradiction_clause,[],[f441])).

fof(f441,plain,
    ( $false
    | ~ spl8_13 ),
    inference(unit_resulting_resolution,[],[f61,f439])).

fof(f439,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f438])).

fof(f291,plain,
    ( ~ spl8_2
    | spl8_5 ),
    inference(avatar_contradiction_clause,[],[f290])).

fof(f290,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f152,f138,f264,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t52_pre_topc.p',d3_tarski)).

fof(f264,plain,
    ( ~ r2_hidden(sK7(k2_pre_topc(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ spl8_2
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f61,f118,f97,f60,f60,f139,f138,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X3,X0)
      | ~ r1_tarski(X1,X3)
      | r2_hidden(X2,X3)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( r2_hidden(X2,X3)
                    | ~ r1_tarski(X1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( r2_hidden(X2,X3)
                    | ~ r1_tarski(X1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( r2_hidden(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( r1_tarski(X1,X3)
                        & v4_pre_topc(X3,X0) )
                     => r2_hidden(X2,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t52_pre_topc.p',t45_pre_topc)).

fof(f139,plain,
    ( ~ r2_hidden(sK7(k2_pre_topc(sK0,sK1),sK1),sK1)
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f137,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f137,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f122,f134,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f134,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl8_5
  <=> k2_pre_topc(sK0,sK1) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f122,plain,(
    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f61,f60,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t52_pre_topc.p',t48_pre_topc)).

fof(f118,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f138,plain,
    ( r2_hidden(sK7(k2_pre_topc(sK0,sK1),sK1),k2_pre_topc(sK0,sK1))
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f137,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f152,plain,(
    r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f121,f86])).

fof(f121,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f61,f60,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t52_pre_topc.p',dt_k2_pre_topc)).

fof(f161,plain,
    ( spl8_4
    | spl8_2 ),
    inference(avatar_split_clause,[],[f59,f117,f130])).

fof(f59,plain,
    ( v4_pre_topc(sK1,sK0)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(cnf_transformation,[],[f33])).

fof(f156,plain,
    ( ~ spl8_3
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f57,f133,f114])).

fof(f57,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f135,plain,
    ( spl8_0
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f56,f133,f111])).

fof(f56,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
