%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:14 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 109 expanded)
%              Number of leaves         :   21 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :  182 ( 322 expanded)
%              Number of equality atoms :   28 (  64 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f109,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f51,f55,f59,f63,f67,f72,f93,f108])).

fof(f108,plain,
    ( spl4_4
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f98,f91,f61,f53,f57])).

fof(f57,plain,
    ( spl4_4
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f53,plain,
    ( spl4_3
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f61,plain,
    ( spl4_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f91,plain,
    ( spl4_8
  <=> k1_xboole_0 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f98,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_8 ),
    inference(superposition,[],[f37,f92])).

fof(f92,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f91])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f93,plain,
    ( spl4_8
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f89,f70,f65,f91])).

fof(f65,plain,
    ( spl4_6
  <=> k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f70,plain,
    ( spl4_7
  <=> m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f89,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(resolution,[],[f87,f71])).

fof(f71,plain,
    ( m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f70])).

fof(f87,plain,
    ( ! [X0] :
        ( ~ m1_setfam_1(k1_xboole_0,X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_6 ),
    inference(resolution,[],[f84,f74])).

fof(f74,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k1_xboole_0)
        | ~ m1_setfam_1(k1_xboole_0,X0) )
    | ~ spl4_6 ),
    inference(superposition,[],[f39,f66])).

fof(f66,plain,
    ( k1_xboole_0 = k3_tarski(k1_xboole_0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ m1_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ m1_setfam_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
    <=> r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

fof(f84,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f83,f36])).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f83,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X4,sK2(X3))
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f77,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f77,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0),X1)
      | ~ r1_tarski(X0,X1)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f40,f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f72,plain,
    ( spl4_7
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f68,f49,f45,f70])).

fof(f45,plain,
    ( spl4_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f49,plain,
    ( spl4_2
  <=> m1_setfam_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f68,plain,
    ( m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(superposition,[],[f50,f46])).

fof(f46,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f50,plain,
    ( m1_setfam_1(sK1,u1_struct_0(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f67,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f35,f65])).

fof(f35,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f63,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f34,f61])).

fof(f34,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f59,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f30,f57])).

fof(f30,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k1_xboole_0 = sK1
    & m1_setfam_1(sK1,u1_struct_0(sK0))
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 = X1
            & m1_setfam_1(X1,u1_struct_0(X0)) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(sK0)) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( k1_xboole_0 = X1
        & m1_setfam_1(X1,u1_struct_0(sK0)) )
   => ( k1_xboole_0 = sK1
      & m1_setfam_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ~ ( k1_xboole_0 = X1
              & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

% (12828)Termination reason: Refutation not found, incomplete strategy
fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ~ ( k1_xboole_0 = X1
                & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

% (12828)Memory used [KB]: 10618
% (12828)Time elapsed: 0.097 s
% (12828)------------------------------
% (12828)------------------------------
% (12819)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ~ ( k1_xboole_0 = X1
              & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).

fof(f55,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f31,f53])).

fof(f31,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f32,f49])).

fof(f32,plain,(
    m1_setfam_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f33,f45])).

fof(f33,plain,(
    k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:53:32 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (812843008)
% 0.13/0.37  ipcrm: permission denied for id (815529987)
% 0.13/0.37  ipcrm: permission denied for id (815562756)
% 0.13/0.37  ipcrm: permission denied for id (815595525)
% 0.13/0.37  ipcrm: permission denied for id (815628294)
% 0.13/0.37  ipcrm: permission denied for id (815661063)
% 0.13/0.37  ipcrm: permission denied for id (815693832)
% 0.13/0.38  ipcrm: permission denied for id (818610185)
% 0.13/0.38  ipcrm: permission denied for id (813006858)
% 0.13/0.38  ipcrm: permission denied for id (813039627)
% 0.13/0.38  ipcrm: permission denied for id (815759372)
% 0.13/0.38  ipcrm: permission denied for id (818642957)
% 0.13/0.38  ipcrm: permission denied for id (815857679)
% 0.13/0.39  ipcrm: permission denied for id (813170704)
% 0.13/0.39  ipcrm: permission denied for id (818708497)
% 0.13/0.39  ipcrm: permission denied for id (813236242)
% 0.13/0.39  ipcrm: permission denied for id (815923219)
% 0.13/0.39  ipcrm: permission denied for id (815955988)
% 0.22/0.39  ipcrm: permission denied for id (818741269)
% 0.22/0.39  ipcrm: permission denied for id (816021526)
% 0.22/0.39  ipcrm: permission denied for id (816054295)
% 0.22/0.40  ipcrm: permission denied for id (816087064)
% 0.22/0.40  ipcrm: permission denied for id (818774041)
% 0.22/0.40  ipcrm: permission denied for id (816152602)
% 0.22/0.40  ipcrm: permission denied for id (816185371)
% 0.22/0.40  ipcrm: permission denied for id (816283678)
% 0.22/0.41  ipcrm: permission denied for id (813432864)
% 0.22/0.41  ipcrm: permission denied for id (813465633)
% 0.22/0.41  ipcrm: permission denied for id (816349218)
% 0.22/0.41  ipcrm: permission denied for id (818905123)
% 0.22/0.41  ipcrm: permission denied for id (816414756)
% 0.22/0.41  ipcrm: permission denied for id (816447525)
% 0.22/0.41  ipcrm: permission denied for id (818937894)
% 0.22/0.41  ipcrm: permission denied for id (816513063)
% 0.22/0.42  ipcrm: permission denied for id (818970664)
% 0.22/0.42  ipcrm: permission denied for id (813596713)
% 0.22/0.42  ipcrm: permission denied for id (813629482)
% 0.22/0.42  ipcrm: permission denied for id (816578603)
% 0.22/0.42  ipcrm: permission denied for id (816611372)
% 0.22/0.42  ipcrm: permission denied for id (813727789)
% 0.22/0.42  ipcrm: permission denied for id (819003438)
% 0.22/0.43  ipcrm: permission denied for id (816709680)
% 0.22/0.43  ipcrm: permission denied for id (816742449)
% 0.22/0.43  ipcrm: permission denied for id (819068978)
% 0.22/0.43  ipcrm: permission denied for id (813793332)
% 0.22/0.43  ipcrm: permission denied for id (816873526)
% 0.22/0.44  ipcrm: permission denied for id (816939064)
% 0.22/0.44  ipcrm: permission denied for id (816971833)
% 0.22/0.44  ipcrm: permission denied for id (817004602)
% 0.22/0.44  ipcrm: permission denied for id (813891643)
% 0.22/0.44  ipcrm: permission denied for id (817037372)
% 0.22/0.44  ipcrm: permission denied for id (819200061)
% 0.22/0.44  ipcrm: permission denied for id (819265599)
% 0.22/0.45  ipcrm: permission denied for id (817168448)
% 0.22/0.45  ipcrm: permission denied for id (814055489)
% 0.22/0.45  ipcrm: permission denied for id (814088258)
% 0.22/0.45  ipcrm: permission denied for id (817201219)
% 0.22/0.45  ipcrm: permission denied for id (819298372)
% 0.22/0.45  ipcrm: permission denied for id (817266757)
% 0.22/0.45  ipcrm: permission denied for id (817299526)
% 0.22/0.45  ipcrm: permission denied for id (814153799)
% 0.22/0.46  ipcrm: permission denied for id (814186568)
% 0.22/0.46  ipcrm: permission denied for id (817332297)
% 0.22/0.46  ipcrm: permission denied for id (819331146)
% 0.22/0.46  ipcrm: permission denied for id (817397835)
% 0.22/0.46  ipcrm: permission denied for id (814252108)
% 0.22/0.46  ipcrm: permission denied for id (817463374)
% 0.22/0.46  ipcrm: permission denied for id (817496143)
% 0.22/0.47  ipcrm: permission denied for id (814317648)
% 0.22/0.47  ipcrm: permission denied for id (817528913)
% 0.22/0.47  ipcrm: permission denied for id (814350418)
% 0.22/0.47  ipcrm: permission denied for id (817594452)
% 0.22/0.47  ipcrm: permission denied for id (814448725)
% 0.22/0.47  ipcrm: permission denied for id (814481494)
% 0.22/0.47  ipcrm: permission denied for id (817627223)
% 0.22/0.48  ipcrm: permission denied for id (819429464)
% 0.22/0.48  ipcrm: permission denied for id (814547033)
% 0.22/0.48  ipcrm: permission denied for id (817692762)
% 0.22/0.48  ipcrm: permission denied for id (814579803)
% 0.22/0.48  ipcrm: permission denied for id (814645341)
% 0.22/0.48  ipcrm: permission denied for id (814678110)
% 0.22/0.48  ipcrm: permission denied for id (814710879)
% 0.22/0.49  ipcrm: permission denied for id (814743649)
% 0.22/0.49  ipcrm: permission denied for id (817791074)
% 0.22/0.49  ipcrm: permission denied for id (819527779)
% 0.22/0.49  ipcrm: permission denied for id (814841957)
% 0.22/0.49  ipcrm: permission denied for id (814874726)
% 0.22/0.49  ipcrm: permission denied for id (819593319)
% 0.22/0.50  ipcrm: permission denied for id (817922152)
% 0.22/0.50  ipcrm: permission denied for id (814907497)
% 0.22/0.50  ipcrm: permission denied for id (814940268)
% 0.22/0.50  ipcrm: permission denied for id (818020461)
% 0.22/0.50  ipcrm: permission denied for id (818085998)
% 0.22/0.51  ipcrm: permission denied for id (815038575)
% 0.22/0.51  ipcrm: permission denied for id (818118768)
% 0.22/0.51  ipcrm: permission denied for id (818184306)
% 0.22/0.51  ipcrm: permission denied for id (819724403)
% 0.22/0.51  ipcrm: permission denied for id (818249844)
% 0.22/0.52  ipcrm: permission denied for id (815235190)
% 0.22/0.52  ipcrm: permission denied for id (815267959)
% 0.36/0.52  ipcrm: permission denied for id (819822713)
% 0.36/0.52  ipcrm: permission denied for id (815333498)
% 0.36/0.52  ipcrm: permission denied for id (818413691)
% 0.36/0.52  ipcrm: permission denied for id (815366268)
% 0.36/0.52  ipcrm: permission denied for id (818446461)
% 0.36/0.53  ipcrm: permission denied for id (819888255)
% 0.40/0.66  % (12836)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.40/0.66  % (12828)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.40/0.67  % (12844)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.40/0.67  % (12836)Refutation found. Thanks to Tanya!
% 0.40/0.67  % SZS status Theorem for theBenchmark
% 0.40/0.67  % (12828)Refutation not found, incomplete strategy% (12828)------------------------------
% 0.40/0.67  % (12828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.40/0.67  % SZS output start Proof for theBenchmark
% 0.40/0.67  fof(f109,plain,(
% 0.40/0.67    $false),
% 0.40/0.67    inference(avatar_sat_refutation,[],[f47,f51,f55,f59,f63,f67,f72,f93,f108])).
% 0.40/0.67  fof(f108,plain,(
% 0.40/0.67    spl4_4 | ~spl4_3 | ~spl4_5 | ~spl4_8),
% 0.40/0.67    inference(avatar_split_clause,[],[f98,f91,f61,f53,f57])).
% 0.40/0.67  fof(f57,plain,(
% 0.40/0.67    spl4_4 <=> v2_struct_0(sK0)),
% 0.40/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.40/0.67  fof(f53,plain,(
% 0.40/0.67    spl4_3 <=> l1_struct_0(sK0)),
% 0.40/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.40/0.67  fof(f61,plain,(
% 0.40/0.67    spl4_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.40/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.40/0.67  fof(f91,plain,(
% 0.40/0.67    spl4_8 <=> k1_xboole_0 = u1_struct_0(sK0)),
% 0.40/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.40/0.67  fof(f98,plain,(
% 0.40/0.67    ~v1_xboole_0(k1_xboole_0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl4_8),
% 0.40/0.67    inference(superposition,[],[f37,f92])).
% 0.40/0.67  fof(f92,plain,(
% 0.40/0.67    k1_xboole_0 = u1_struct_0(sK0) | ~spl4_8),
% 0.40/0.67    inference(avatar_component_clause,[],[f91])).
% 0.40/0.67  fof(f37,plain,(
% 0.40/0.67    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.40/0.67    inference(cnf_transformation,[],[f16])).
% 0.40/0.67  fof(f16,plain,(
% 0.40/0.67    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.40/0.67    inference(flattening,[],[f15])).
% 0.40/0.67  fof(f15,plain,(
% 0.40/0.67    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.40/0.67    inference(ennf_transformation,[],[f8])).
% 0.40/0.67  fof(f8,axiom,(
% 0.40/0.67    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.40/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.40/0.67  fof(f93,plain,(
% 0.40/0.67    spl4_8 | ~spl4_6 | ~spl4_7),
% 0.40/0.67    inference(avatar_split_clause,[],[f89,f70,f65,f91])).
% 0.40/0.67  fof(f65,plain,(
% 0.40/0.67    spl4_6 <=> k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.40/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.40/0.67  fof(f70,plain,(
% 0.40/0.67    spl4_7 <=> m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))),
% 0.40/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.40/0.67  fof(f89,plain,(
% 0.40/0.67    k1_xboole_0 = u1_struct_0(sK0) | (~spl4_6 | ~spl4_7)),
% 0.40/0.67    inference(resolution,[],[f87,f71])).
% 0.40/0.67  fof(f71,plain,(
% 0.40/0.67    m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) | ~spl4_7),
% 0.40/0.67    inference(avatar_component_clause,[],[f70])).
% 0.40/0.67  fof(f87,plain,(
% 0.40/0.67    ( ! [X0] : (~m1_setfam_1(k1_xboole_0,X0) | k1_xboole_0 = X0) ) | ~spl4_6),
% 0.40/0.67    inference(resolution,[],[f84,f74])).
% 0.40/0.67  fof(f74,plain,(
% 0.40/0.67    ( ! [X0] : (r1_tarski(X0,k1_xboole_0) | ~m1_setfam_1(k1_xboole_0,X0)) ) | ~spl4_6),
% 0.40/0.67    inference(superposition,[],[f39,f66])).
% 0.40/0.67  fof(f66,plain,(
% 0.40/0.67    k1_xboole_0 = k3_tarski(k1_xboole_0) | ~spl4_6),
% 0.40/0.67    inference(avatar_component_clause,[],[f65])).
% 0.40/0.67  fof(f39,plain,(
% 0.40/0.67    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)) )),
% 0.40/0.67    inference(cnf_transformation,[],[f18])).
% 0.40/0.67  fof(f18,plain,(
% 0.40/0.67    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0))),
% 0.40/0.67    inference(ennf_transformation,[],[f11])).
% 0.40/0.67  fof(f11,plain,(
% 0.40/0.67    ! [X0,X1] : (m1_setfam_1(X1,X0) => r1_tarski(X0,k3_tarski(X1)))),
% 0.40/0.67    inference(unused_predicate_definition_removal,[],[f6])).
% 0.40/0.67  fof(f6,axiom,(
% 0.40/0.67    ! [X0,X1] : (m1_setfam_1(X1,X0) <=> r1_tarski(X0,k3_tarski(X1)))),
% 0.40/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).
% 0.40/0.67  fof(f84,plain,(
% 0.40/0.67    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.40/0.67    inference(resolution,[],[f83,f36])).
% 0.40/0.67  fof(f36,plain,(
% 0.40/0.67    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.40/0.67    inference(cnf_transformation,[],[f4])).
% 0.40/0.67  fof(f4,axiom,(
% 0.40/0.67    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.40/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.40/0.67  fof(f83,plain,(
% 0.40/0.67    ( ! [X4,X3] : (~r1_tarski(X4,sK2(X3)) | k1_xboole_0 = X3 | ~r1_tarski(X3,X4)) )),
% 0.40/0.67    inference(resolution,[],[f77,f43])).
% 0.40/0.67  fof(f43,plain,(
% 0.40/0.67    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.40/0.67    inference(cnf_transformation,[],[f20])).
% 0.40/0.67  fof(f20,plain,(
% 0.40/0.67    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.40/0.67    inference(ennf_transformation,[],[f7])).
% 0.40/0.67  fof(f7,axiom,(
% 0.40/0.67    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.40/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.40/0.67  fof(f77,plain,(
% 0.40/0.67    ( ! [X0,X1] : (r2_hidden(sK2(X0),X1) | ~r1_tarski(X0,X1) | k1_xboole_0 = X0) )),
% 0.40/0.67    inference(resolution,[],[f40,f38])).
% 0.40/0.67  fof(f38,plain,(
% 0.40/0.67    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.40/0.67    inference(cnf_transformation,[],[f25])).
% 0.40/0.67  fof(f25,plain,(
% 0.40/0.67    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.40/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f24])).
% 0.40/0.67  fof(f24,plain,(
% 0.40/0.67    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.40/0.67    introduced(choice_axiom,[])).
% 0.40/0.67  fof(f17,plain,(
% 0.40/0.67    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.40/0.67    inference(ennf_transformation,[],[f3])).
% 0.40/0.67  fof(f3,axiom,(
% 0.40/0.67    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.40/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.40/0.67  fof(f40,plain,(
% 0.40/0.67    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.40/0.67    inference(cnf_transformation,[],[f29])).
% 0.40/0.67  fof(f29,plain,(
% 0.40/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.40/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).
% 0.40/0.67  fof(f28,plain,(
% 0.40/0.67    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.40/0.67    introduced(choice_axiom,[])).
% 0.40/0.67  fof(f27,plain,(
% 0.40/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.40/0.67    inference(rectify,[],[f26])).
% 0.40/0.67  fof(f26,plain,(
% 0.40/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.40/0.67    inference(nnf_transformation,[],[f19])).
% 0.40/0.67  fof(f19,plain,(
% 0.40/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.40/0.67    inference(ennf_transformation,[],[f1])).
% 0.40/0.67  fof(f1,axiom,(
% 0.40/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.40/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.40/0.67  fof(f72,plain,(
% 0.40/0.67    spl4_7 | ~spl4_1 | ~spl4_2),
% 0.40/0.67    inference(avatar_split_clause,[],[f68,f49,f45,f70])).
% 0.40/0.67  fof(f45,plain,(
% 0.40/0.67    spl4_1 <=> k1_xboole_0 = sK1),
% 0.40/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.40/0.67  fof(f49,plain,(
% 0.40/0.67    spl4_2 <=> m1_setfam_1(sK1,u1_struct_0(sK0))),
% 0.40/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.40/0.67  fof(f68,plain,(
% 0.40/0.67    m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) | (~spl4_1 | ~spl4_2)),
% 0.40/0.67    inference(superposition,[],[f50,f46])).
% 0.40/0.67  fof(f46,plain,(
% 0.40/0.67    k1_xboole_0 = sK1 | ~spl4_1),
% 0.40/0.67    inference(avatar_component_clause,[],[f45])).
% 0.40/0.67  fof(f50,plain,(
% 0.40/0.67    m1_setfam_1(sK1,u1_struct_0(sK0)) | ~spl4_2),
% 0.40/0.67    inference(avatar_component_clause,[],[f49])).
% 0.40/0.67  fof(f67,plain,(
% 0.40/0.67    spl4_6),
% 0.40/0.67    inference(avatar_split_clause,[],[f35,f65])).
% 0.40/0.67  fof(f35,plain,(
% 0.40/0.67    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.40/0.67    inference(cnf_transformation,[],[f5])).
% 0.40/0.67  fof(f5,axiom,(
% 0.40/0.67    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.40/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.40/0.67  fof(f63,plain,(
% 0.40/0.67    spl4_5),
% 0.40/0.67    inference(avatar_split_clause,[],[f34,f61])).
% 0.40/0.67  fof(f34,plain,(
% 0.40/0.67    v1_xboole_0(k1_xboole_0)),
% 0.40/0.67    inference(cnf_transformation,[],[f2])).
% 0.40/0.67  fof(f2,axiom,(
% 0.40/0.67    v1_xboole_0(k1_xboole_0)),
% 0.40/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.40/0.67  fof(f59,plain,(
% 0.40/0.67    ~spl4_4),
% 0.40/0.67    inference(avatar_split_clause,[],[f30,f57])).
% 0.40/0.67  fof(f30,plain,(
% 0.40/0.67    ~v2_struct_0(sK0)),
% 0.40/0.67    inference(cnf_transformation,[],[f23])).
% 0.40/0.67  fof(f23,plain,(
% 0.40/0.67    (k1_xboole_0 = sK1 & m1_setfam_1(sK1,u1_struct_0(sK0))) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.40/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f22,f21])).
% 0.40/0.67  fof(f21,plain,(
% 0.40/0.67    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(sK0))) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.40/0.67    introduced(choice_axiom,[])).
% 0.40/0.67  fof(f22,plain,(
% 0.40/0.67    ? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(sK0))) => (k1_xboole_0 = sK1 & m1_setfam_1(sK1,u1_struct_0(sK0)))),
% 0.40/0.67    introduced(choice_axiom,[])).
% 0.40/0.67  fof(f14,plain,(
% 0.40/0.67    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.40/0.67    inference(flattening,[],[f13])).
% 0.40/0.67  fof(f13,plain,(
% 0.40/0.67    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.40/0.67    inference(ennf_transformation,[],[f12])).
% 0.40/0.67  fof(f12,plain,(
% 0.40/0.67    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))))),
% 0.40/0.67    inference(pure_predicate_removal,[],[f10])).
% 0.40/0.67  % (12828)Termination reason: Refutation not found, incomplete strategy
% 0.40/0.67  fof(f10,negated_conjecture,(
% 0.40/0.67    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 0.40/0.67    inference(negated_conjecture,[],[f9])).
% 0.40/0.67  
% 0.40/0.67  % (12828)Memory used [KB]: 10618
% 0.40/0.67  % (12828)Time elapsed: 0.097 s
% 0.40/0.67  % (12828)------------------------------
% 0.40/0.67  % (12828)------------------------------
% 0.40/0.67  % (12819)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.40/0.67  fof(f9,conjecture,(
% 0.40/0.67    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 0.40/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).
% 0.40/0.67  fof(f55,plain,(
% 0.40/0.67    spl4_3),
% 0.40/0.67    inference(avatar_split_clause,[],[f31,f53])).
% 0.40/0.68  fof(f31,plain,(
% 0.40/0.68    l1_struct_0(sK0)),
% 0.40/0.68    inference(cnf_transformation,[],[f23])).
% 0.40/0.68  fof(f51,plain,(
% 0.40/0.68    spl4_2),
% 0.40/0.68    inference(avatar_split_clause,[],[f32,f49])).
% 0.40/0.68  fof(f32,plain,(
% 0.40/0.68    m1_setfam_1(sK1,u1_struct_0(sK0))),
% 0.40/0.68    inference(cnf_transformation,[],[f23])).
% 0.40/0.68  fof(f47,plain,(
% 0.40/0.68    spl4_1),
% 0.40/0.68    inference(avatar_split_clause,[],[f33,f45])).
% 0.40/0.68  fof(f33,plain,(
% 0.40/0.68    k1_xboole_0 = sK1),
% 0.40/0.68    inference(cnf_transformation,[],[f23])).
% 0.40/0.68  % SZS output end Proof for theBenchmark
% 0.40/0.68  % (12836)------------------------------
% 0.40/0.68  % (12836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.40/0.68  % (12836)Termination reason: Refutation
% 0.40/0.68  
% 0.40/0.68  % (12836)Memory used [KB]: 10746
% 0.40/0.68  % (12836)Time elapsed: 0.100 s
% 0.40/0.68  % (12836)------------------------------
% 0.40/0.68  % (12836)------------------------------
% 0.40/0.68  % (12661)Success in time 0.317 s
%------------------------------------------------------------------------------
