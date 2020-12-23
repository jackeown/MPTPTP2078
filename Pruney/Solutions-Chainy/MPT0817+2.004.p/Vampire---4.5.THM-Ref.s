%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:15 EST 2020

% Result     : Theorem 1.17s
% Output     : Refutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :   57 (  95 expanded)
%              Number of leaves         :   15 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :  145 ( 240 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f74,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f44,f50,f56,f62,f69,f73])).

fof(f73,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | spl4_7 ),
    inference(unit_resulting_resolution,[],[f24,f25,f68,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f68,plain,
    ( ~ v5_relat_1(k2_zfmisc_1(sK0,sK2),sK2)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl4_7
  <=> v5_relat_1(k2_zfmisc_1(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).

fof(f24,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f69,plain,
    ( ~ spl4_7
    | ~ spl4_3
    | spl4_6 ),
    inference(avatar_split_clause,[],[f63,f59,f41,f66])).

fof(f41,plain,
    ( spl4_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f59,plain,
    ( spl4_6
  <=> v5_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f63,plain,
    ( ~ v5_relat_1(k2_zfmisc_1(sK0,sK2),sK2)
    | ~ spl4_3
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f24,f43,f61,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v5_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_relat_1)).

fof(f61,plain,
    ( ~ v5_relat_1(sK3,sK2)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f43,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f62,plain,
    ( ~ spl4_6
    | ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f57,f53,f47,f59])).

fof(f47,plain,
    ( spl4_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f53,plain,
    ( spl4_5
  <=> r1_tarski(k2_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f57,plain,
    ( ~ v5_relat_1(sK3,sK2)
    | ~ spl4_4
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f49,f55,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f55,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f49,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f56,plain,
    ( ~ spl4_5
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f51,f47,f36,f31,f53])).

fof(f31,plain,
    ( spl4_1
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f36,plain,
    ( spl4_2
  <=> r1_tarski(k1_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f51,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f38,f33,f49,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f33,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f38,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f50,plain,
    ( spl4_4
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f45,f41,f47])).

fof(f45,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f24,f43,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f44,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f20,f41])).

fof(f20,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & r1_tarski(k1_relat_1(sK3),sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & r1_tarski(k1_relat_1(X3),X1)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
   => ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & r1_tarski(k1_relat_1(sK3),sK1)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & r1_tarski(k1_relat_1(X3),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & r1_tarski(k1_relat_1(X3),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => ( r1_tarski(k1_relat_1(X3),X1)
         => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

fof(f39,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f21,f36])).

fof(f21,plain,(
    r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f34,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f22,f31])).

fof(f22,plain,(
    ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:01:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (810975232)
% 0.14/0.37  ipcrm: permission denied for id (811008001)
% 0.14/0.37  ipcrm: permission denied for id (811073539)
% 0.14/0.37  ipcrm: permission denied for id (814284804)
% 0.14/0.37  ipcrm: permission denied for id (814317573)
% 0.14/0.37  ipcrm: permission denied for id (814350342)
% 0.14/0.38  ipcrm: permission denied for id (811204616)
% 0.14/0.38  ipcrm: permission denied for id (811237385)
% 0.14/0.38  ipcrm: permission denied for id (814481420)
% 0.14/0.38  ipcrm: permission denied for id (816873485)
% 0.14/0.38  ipcrm: permission denied for id (814546958)
% 0.14/0.38  ipcrm: permission denied for id (814579727)
% 0.14/0.39  ipcrm: permission denied for id (816906256)
% 0.14/0.39  ipcrm: permission denied for id (811368465)
% 0.14/0.39  ipcrm: permission denied for id (814645266)
% 0.14/0.39  ipcrm: permission denied for id (811434003)
% 0.14/0.39  ipcrm: permission denied for id (814710805)
% 0.14/0.39  ipcrm: permission denied for id (816971798)
% 0.14/0.39  ipcrm: permission denied for id (817004567)
% 0.14/0.40  ipcrm: permission denied for id (814809112)
% 0.14/0.40  ipcrm: permission denied for id (811565081)
% 0.14/0.40  ipcrm: permission denied for id (811597851)
% 0.14/0.40  ipcrm: permission denied for id (814874652)
% 0.14/0.40  ipcrm: permission denied for id (814907421)
% 0.22/0.40  ipcrm: permission denied for id (814940190)
% 0.22/0.40  ipcrm: permission denied for id (811663391)
% 0.22/0.41  ipcrm: permission denied for id (811696160)
% 0.22/0.41  ipcrm: permission denied for id (811728929)
% 0.22/0.41  ipcrm: permission denied for id (811761698)
% 0.22/0.41  ipcrm: permission denied for id (815005732)
% 0.22/0.41  ipcrm: permission denied for id (815038501)
% 0.22/0.41  ipcrm: permission denied for id (815071270)
% 0.22/0.41  ipcrm: permission denied for id (811892775)
% 0.22/0.42  ipcrm: permission denied for id (811925544)
% 0.22/0.42  ipcrm: permission denied for id (811958313)
% 0.22/0.42  ipcrm: permission denied for id (811991082)
% 0.22/0.42  ipcrm: permission denied for id (812023851)
% 0.22/0.42  ipcrm: permission denied for id (812056620)
% 0.22/0.42  ipcrm: permission denied for id (812089390)
% 0.22/0.43  ipcrm: permission denied for id (817168432)
% 0.22/0.43  ipcrm: permission denied for id (815202353)
% 0.22/0.43  ipcrm: permission denied for id (815235122)
% 0.22/0.43  ipcrm: permission denied for id (812220468)
% 0.22/0.43  ipcrm: permission denied for id (817233973)
% 0.22/0.43  ipcrm: permission denied for id (812253238)
% 0.22/0.43  ipcrm: permission denied for id (812286007)
% 0.22/0.44  ipcrm: permission denied for id (815366201)
% 0.22/0.44  ipcrm: permission denied for id (812384314)
% 0.22/0.44  ipcrm: permission denied for id (812449852)
% 0.22/0.44  ipcrm: permission denied for id (812482621)
% 0.22/0.44  ipcrm: permission denied for id (815431742)
% 0.22/0.44  ipcrm: permission denied for id (812548159)
% 0.22/0.45  ipcrm: permission denied for id (817332288)
% 0.22/0.45  ipcrm: permission denied for id (812580929)
% 0.22/0.45  ipcrm: permission denied for id (817397827)
% 0.22/0.45  ipcrm: permission denied for id (812646468)
% 0.22/0.45  ipcrm: permission denied for id (812679237)
% 0.22/0.45  ipcrm: permission denied for id (812712006)
% 0.22/0.45  ipcrm: permission denied for id (812744775)
% 0.22/0.46  ipcrm: permission denied for id (815562824)
% 0.22/0.46  ipcrm: permission denied for id (817430601)
% 0.22/0.46  ipcrm: permission denied for id (812810314)
% 0.22/0.46  ipcrm: permission denied for id (812843083)
% 0.22/0.46  ipcrm: permission denied for id (812875852)
% 0.22/0.46  ipcrm: permission denied for id (817463373)
% 0.22/0.46  ipcrm: permission denied for id (815661134)
% 0.22/0.47  ipcrm: permission denied for id (815759441)
% 0.22/0.47  ipcrm: permission denied for id (812974162)
% 0.22/0.47  ipcrm: permission denied for id (813039700)
% 0.22/0.47  ipcrm: permission denied for id (815857749)
% 0.22/0.47  ipcrm: permission denied for id (813105238)
% 0.22/0.47  ipcrm: permission denied for id (813138007)
% 0.22/0.48  ipcrm: permission denied for id (815890520)
% 0.22/0.48  ipcrm: permission denied for id (815923289)
% 0.22/0.48  ipcrm: permission denied for id (813236316)
% 0.22/0.48  ipcrm: permission denied for id (813269085)
% 0.22/0.48  ipcrm: permission denied for id (816021598)
% 0.22/0.48  ipcrm: permission denied for id (816054367)
% 0.22/0.49  ipcrm: permission denied for id (813367392)
% 0.22/0.49  ipcrm: permission denied for id (817660001)
% 0.22/0.49  ipcrm: permission denied for id (813432930)
% 0.22/0.49  ipcrm: permission denied for id (817692771)
% 0.22/0.49  ipcrm: permission denied for id (817725540)
% 0.22/0.49  ipcrm: permission denied for id (816185445)
% 0.22/0.49  ipcrm: permission denied for id (817758310)
% 0.22/0.49  ipcrm: permission denied for id (816250983)
% 0.22/0.50  ipcrm: permission denied for id (816283752)
% 0.22/0.50  ipcrm: permission denied for id (817791081)
% 0.22/0.50  ipcrm: permission denied for id (813629546)
% 0.22/0.50  ipcrm: permission denied for id (813662315)
% 0.22/0.50  ipcrm: permission denied for id (813695084)
% 0.22/0.50  ipcrm: permission denied for id (813727853)
% 0.22/0.50  ipcrm: permission denied for id (813760622)
% 0.22/0.50  ipcrm: permission denied for id (817823855)
% 0.22/0.51  ipcrm: permission denied for id (816382064)
% 0.22/0.51  ipcrm: permission denied for id (813858930)
% 0.22/0.51  ipcrm: permission denied for id (813957236)
% 0.22/0.51  ipcrm: permission denied for id (813990005)
% 0.22/0.51  ipcrm: permission denied for id (817922166)
% 0.22/0.51  ipcrm: permission denied for id (817954935)
% 0.22/0.51  ipcrm: permission denied for id (816578680)
% 0.22/0.52  ipcrm: permission denied for id (817987705)
% 0.22/0.52  ipcrm: permission denied for id (816644218)
% 0.22/0.52  ipcrm: permission denied for id (818020475)
% 0.22/0.52  ipcrm: permission denied for id (814153852)
% 0.22/0.52  ipcrm: permission denied for id (816709757)
% 0.22/0.52  ipcrm: permission denied for id (814186622)
% 0.22/0.52  ipcrm: permission denied for id (814219391)
% 0.22/0.58  % (32705)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 1.17/0.66  % (32705)Refutation found. Thanks to Tanya!
% 1.17/0.66  % SZS status Theorem for theBenchmark
% 1.17/0.66  % SZS output start Proof for theBenchmark
% 1.17/0.66  fof(f74,plain,(
% 1.17/0.66    $false),
% 1.17/0.66    inference(avatar_sat_refutation,[],[f34,f39,f44,f50,f56,f62,f69,f73])).
% 1.17/0.66  fof(f73,plain,(
% 1.17/0.66    spl4_7),
% 1.17/0.66    inference(avatar_contradiction_clause,[],[f72])).
% 1.17/0.66  fof(f72,plain,(
% 1.17/0.66    $false | spl4_7),
% 1.17/0.66    inference(unit_resulting_resolution,[],[f24,f25,f68,f27])).
% 1.17/0.66  fof(f27,plain,(
% 1.17/0.66    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.17/0.66    inference(cnf_transformation,[],[f19])).
% 1.17/0.66  fof(f19,plain,(
% 1.17/0.66    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.17/0.66    inference(nnf_transformation,[],[f12])).
% 1.17/0.66  fof(f12,plain,(
% 1.17/0.66    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.17/0.66    inference(ennf_transformation,[],[f3])).
% 1.17/0.66  fof(f3,axiom,(
% 1.17/0.66    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.17/0.66  fof(f68,plain,(
% 1.17/0.66    ~v5_relat_1(k2_zfmisc_1(sK0,sK2),sK2) | spl4_7),
% 1.17/0.66    inference(avatar_component_clause,[],[f66])).
% 1.17/0.66  fof(f66,plain,(
% 1.17/0.66    spl4_7 <=> v5_relat_1(k2_zfmisc_1(sK0,sK2),sK2)),
% 1.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.17/0.66  fof(f25,plain,(
% 1.17/0.66    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)) )),
% 1.17/0.66    inference(cnf_transformation,[],[f5])).
% 1.17/0.66  fof(f5,axiom,(
% 1.17/0.66    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)),
% 1.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).
% 1.17/0.66  fof(f24,plain,(
% 1.17/0.66    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.17/0.66    inference(cnf_transformation,[],[f4])).
% 1.17/0.66  fof(f4,axiom,(
% 1.17/0.66    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.17/0.66  fof(f69,plain,(
% 1.17/0.66    ~spl4_7 | ~spl4_3 | spl4_6),
% 1.17/0.66    inference(avatar_split_clause,[],[f63,f59,f41,f66])).
% 1.17/0.66  fof(f41,plain,(
% 1.17/0.66    spl4_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.17/0.66  fof(f59,plain,(
% 1.17/0.66    spl4_6 <=> v5_relat_1(sK3,sK2)),
% 1.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.17/0.66  fof(f63,plain,(
% 1.17/0.66    ~v5_relat_1(k2_zfmisc_1(sK0,sK2),sK2) | (~spl4_3 | spl4_6)),
% 1.17/0.66    inference(unit_resulting_resolution,[],[f24,f43,f61,f28])).
% 1.17/0.66  fof(f28,plain,(
% 1.17/0.66    ( ! [X2,X0,X1] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.17/0.66    inference(cnf_transformation,[],[f14])).
% 1.17/0.66  fof(f14,plain,(
% 1.17/0.66    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.17/0.66    inference(flattening,[],[f13])).
% 1.17/0.66  fof(f13,plain,(
% 1.17/0.66    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.17/0.66    inference(ennf_transformation,[],[f2])).
% 1.17/0.66  fof(f2,axiom,(
% 1.17/0.66    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X1)) => v5_relat_1(X2,X0)))),
% 1.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_relat_1)).
% 1.17/0.66  fof(f61,plain,(
% 1.17/0.66    ~v5_relat_1(sK3,sK2) | spl4_6),
% 1.17/0.66    inference(avatar_component_clause,[],[f59])).
% 1.17/0.66  fof(f43,plain,(
% 1.17/0.66    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl4_3),
% 1.17/0.66    inference(avatar_component_clause,[],[f41])).
% 1.17/0.66  fof(f62,plain,(
% 1.17/0.66    ~spl4_6 | ~spl4_4 | spl4_5),
% 1.17/0.66    inference(avatar_split_clause,[],[f57,f53,f47,f59])).
% 1.17/0.66  fof(f47,plain,(
% 1.17/0.66    spl4_4 <=> v1_relat_1(sK3)),
% 1.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.17/0.66  fof(f53,plain,(
% 1.17/0.66    spl4_5 <=> r1_tarski(k2_relat_1(sK3),sK2)),
% 1.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.17/0.66  fof(f57,plain,(
% 1.17/0.66    ~v5_relat_1(sK3,sK2) | (~spl4_4 | spl4_5)),
% 1.17/0.66    inference(unit_resulting_resolution,[],[f49,f55,f26])).
% 1.17/0.66  fof(f26,plain,(
% 1.17/0.66    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.17/0.66    inference(cnf_transformation,[],[f19])).
% 1.17/0.66  fof(f55,plain,(
% 1.17/0.66    ~r1_tarski(k2_relat_1(sK3),sK2) | spl4_5),
% 1.17/0.66    inference(avatar_component_clause,[],[f53])).
% 1.17/0.66  fof(f49,plain,(
% 1.17/0.66    v1_relat_1(sK3) | ~spl4_4),
% 1.17/0.66    inference(avatar_component_clause,[],[f47])).
% 1.17/0.66  fof(f56,plain,(
% 1.17/0.66    ~spl4_5 | spl4_1 | ~spl4_2 | ~spl4_4),
% 1.17/0.66    inference(avatar_split_clause,[],[f51,f47,f36,f31,f53])).
% 1.17/0.66  fof(f31,plain,(
% 1.17/0.66    spl4_1 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.17/0.66  fof(f36,plain,(
% 1.17/0.66    spl4_2 <=> r1_tarski(k1_relat_1(sK3),sK1)),
% 1.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.17/0.66  fof(f51,plain,(
% 1.17/0.66    ~r1_tarski(k2_relat_1(sK3),sK2) | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 1.17/0.66    inference(unit_resulting_resolution,[],[f38,f33,f49,f29])).
% 1.17/0.66  fof(f29,plain,(
% 1.17/0.66    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.17/0.66    inference(cnf_transformation,[],[f16])).
% 1.17/0.66  fof(f16,plain,(
% 1.17/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.17/0.66    inference(flattening,[],[f15])).
% 1.17/0.66  fof(f15,plain,(
% 1.17/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.17/0.66    inference(ennf_transformation,[],[f6])).
% 1.17/0.66  fof(f6,axiom,(
% 1.17/0.66    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 1.17/0.66  fof(f33,plain,(
% 1.17/0.66    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl4_1),
% 1.17/0.66    inference(avatar_component_clause,[],[f31])).
% 1.17/0.66  fof(f38,plain,(
% 1.17/0.66    r1_tarski(k1_relat_1(sK3),sK1) | ~spl4_2),
% 1.17/0.66    inference(avatar_component_clause,[],[f36])).
% 1.17/0.66  fof(f50,plain,(
% 1.17/0.66    spl4_4 | ~spl4_3),
% 1.17/0.66    inference(avatar_split_clause,[],[f45,f41,f47])).
% 1.17/0.66  fof(f45,plain,(
% 1.17/0.66    v1_relat_1(sK3) | ~spl4_3),
% 1.17/0.66    inference(unit_resulting_resolution,[],[f24,f43,f23])).
% 1.17/0.66  fof(f23,plain,(
% 1.17/0.66    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.17/0.66    inference(cnf_transformation,[],[f11])).
% 1.17/0.66  fof(f11,plain,(
% 1.17/0.66    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.17/0.66    inference(ennf_transformation,[],[f1])).
% 1.17/0.66  fof(f1,axiom,(
% 1.17/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.17/0.66  fof(f44,plain,(
% 1.17/0.66    spl4_3),
% 1.17/0.66    inference(avatar_split_clause,[],[f20,f41])).
% 1.17/0.66  fof(f20,plain,(
% 1.17/0.66    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.17/0.66    inference(cnf_transformation,[],[f18])).
% 1.17/0.66  fof(f18,plain,(
% 1.17/0.66    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & r1_tarski(k1_relat_1(sK3),sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.17/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f17])).
% 1.17/0.66  fof(f17,plain,(
% 1.17/0.66    ? [X0,X1,X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & r1_tarski(k1_relat_1(X3),X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) => (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & r1_tarski(k1_relat_1(sK3),sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))))),
% 1.17/0.66    introduced(choice_axiom,[])).
% 1.17/0.66  fof(f10,plain,(
% 1.17/0.66    ? [X0,X1,X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & r1_tarski(k1_relat_1(X3),X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.17/0.66    inference(flattening,[],[f9])).
% 1.17/0.66  fof(f9,plain,(
% 1.17/0.66    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & r1_tarski(k1_relat_1(X3),X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.17/0.66    inference(ennf_transformation,[],[f8])).
% 1.17/0.66  fof(f8,negated_conjecture,(
% 1.17/0.66    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 1.17/0.66    inference(negated_conjecture,[],[f7])).
% 1.17/0.66  fof(f7,conjecture,(
% 1.17/0.66    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 1.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).
% 1.17/0.66  fof(f39,plain,(
% 1.17/0.66    spl4_2),
% 1.17/0.66    inference(avatar_split_clause,[],[f21,f36])).
% 1.17/0.66  fof(f21,plain,(
% 1.17/0.66    r1_tarski(k1_relat_1(sK3),sK1)),
% 1.17/0.66    inference(cnf_transformation,[],[f18])).
% 1.17/0.66  fof(f34,plain,(
% 1.17/0.66    ~spl4_1),
% 1.17/0.66    inference(avatar_split_clause,[],[f22,f31])).
% 1.17/0.66  fof(f22,plain,(
% 1.17/0.66    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.17/0.66    inference(cnf_transformation,[],[f18])).
% 1.17/0.66  % SZS output end Proof for theBenchmark
% 1.17/0.66  % (32705)------------------------------
% 1.17/0.66  % (32705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.66  % (32705)Termination reason: Refutation
% 1.17/0.66  
% 1.17/0.66  % (32705)Memory used [KB]: 5373
% 1.17/0.66  % (32705)Time elapsed: 0.075 s
% 1.17/0.66  % (32705)------------------------------
% 1.17/0.66  % (32705)------------------------------
% 1.17/0.66  % (32555)Success in time 0.299 s
%------------------------------------------------------------------------------
