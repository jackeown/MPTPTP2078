%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 215 expanded)
%              Number of leaves         :   11 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  256 ( 690 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f191,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f44,f127,f160,f167,f190])).

fof(f190,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f188,f179])).

fof(f179,plain,
    ( ~ v3_pre_topc(sK2(sK0,sK1),sK0)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f74,f36])).

fof(f36,plain,
    ( ~ v1_tops_2(sK1,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl4_1
  <=> v1_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f74,plain,
    ( ~ v3_pre_topc(sK2(sK0,sK1),sK0)
    | v1_tops_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f72,f20])).

fof(f20,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_2(X1,X0)
          <~> r1_tarski(X1,u1_pre_topc(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v1_tops_2(X1,X0)
            <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tops_2)).

fof(f72,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v3_pre_topc(sK2(sK0,sK1),sK0)
    | v1_tops_2(sK1,sK0) ),
    inference(resolution,[],[f27,f19])).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(sK2(X0,X1),X0)
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).

fof(f188,plain,
    ( v3_pre_topc(sK2(sK0,sK1),sK0)
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f187,f175])).

fof(f175,plain,
    ( r2_hidden(sK2(sK0,sK1),u1_pre_topc(sK0))
    | spl4_1
    | ~ spl4_2 ),
    inference(resolution,[],[f174,f172])).

fof(f172,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK1)
        | r2_hidden(X2,u1_pre_topc(sK0)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f169,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f169,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_pre_topc(sK0)))
    | ~ spl4_2 ),
    inference(resolution,[],[f41,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f41,plain,
    ( r1_tarski(sK1,u1_pre_topc(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl4_2
  <=> r1_tarski(sK1,u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f174,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f57,f36])).

fof(f57,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | v1_tops_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f55,f20])).

fof(f55,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(sK2(sK0,sK1),sK1)
    | v1_tops_2(sK1,sK0) ),
    inference(resolution,[],[f26,f19])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK2(X0,X1),X1)
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f187,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),u1_pre_topc(sK0))
    | v3_pre_topc(sK2(sK0,sK1),sK0)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f182,f20])).

fof(f182,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ r2_hidden(sK2(sK0,sK1),u1_pre_topc(sK0))
    | v3_pre_topc(sK2(sK0,sK1),sK0)
    | spl4_1 ),
    inference(resolution,[],[f180,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f180,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f168,f36])).

fof(f168,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f130,f20])).

fof(f130,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_2(sK1,sK0) ),
    inference(resolution,[],[f25,f19])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f167,plain,
    ( spl4_2
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | spl4_2
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f165,f40])).

fof(f40,plain,
    ( ~ r1_tarski(sK1,u1_pre_topc(sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f165,plain,
    ( r1_tarski(sK1,u1_pre_topc(sK0))
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f164,f19])).

fof(f164,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r1_tarski(sK1,u1_pre_topc(sK0))
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f161,f48])).

fof(f48,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f21,f20])).

fof(f21,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f161,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r1_tarski(sK1,u1_pre_topc(sK0))
    | ~ spl4_9 ),
    inference(resolution,[],[f126,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

fof(f126,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),u1_pre_topc(sK0))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl4_9
  <=> r2_hidden(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f160,plain,
    ( ~ spl4_1
    | spl4_2
    | spl4_8 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | ~ spl4_1
    | spl4_2
    | spl4_8 ),
    inference(subsumption_resolution,[],[f158,f122])).

fof(f122,plain,
    ( ~ v3_pre_topc(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),sK0)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl4_8
  <=> v3_pre_topc(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f158,plain,
    ( v3_pre_topc(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),sK0)
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f157,f93])).

fof(f93,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),sK1)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f92,f40])).

fof(f92,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),sK1)
    | r1_tarski(sK1,u1_pre_topc(sK0)) ),
    inference(resolution,[],[f89,f48])).

fof(f89,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | r2_hidden(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0),sK1)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f30,f19])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f157,plain,
    ( ~ r2_hidden(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),sK1)
    | v3_pre_topc(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),sK0)
    | ~ spl4_1
    | spl4_2 ),
    inference(resolution,[],[f156,f109])).

fof(f109,plain,
    ( m1_subset_1(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_2 ),
    inference(subsumption_resolution,[],[f108,f40])).

fof(f108,plain,
    ( m1_subset_1(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_pre_topc(sK0)) ),
    inference(resolution,[],[f76,f48])).

fof(f76,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | m1_subset_1(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f29,f19])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(sK3(X0,X1,X2),X0)
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f156,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1)
        | v3_pre_topc(X0,sK0) )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f155,f37])).

fof(f37,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f155,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,sK1)
      | v3_pre_topc(X0,sK0)
      | ~ v1_tops_2(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f153,f20])).

fof(f153,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,sK1)
      | v3_pre_topc(X0,sK0)
      | ~ v1_tops_2(sK1,sK0) ) ),
    inference(resolution,[],[f24,f19])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | v3_pre_topc(X2,X0)
      | ~ v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f127,plain,
    ( ~ spl4_8
    | spl4_9
    | spl4_2 ),
    inference(avatar_split_clause,[],[f116,f39,f124,f120])).

fof(f116,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),u1_pre_topc(sK0))
    | ~ v3_pre_topc(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),sK0)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f110,f20])).

fof(f110,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),u1_pre_topc(sK0))
    | ~ v3_pre_topc(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),sK0)
    | spl4_2 ),
    inference(resolution,[],[f109,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f44,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f43,f39,f35])).

fof(f43,plain,
    ( ~ v1_tops_2(sK1,sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f18,f41])).

fof(f18,plain,
    ( ~ r1_tarski(sK1,u1_pre_topc(sK0))
    | ~ v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f42,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f17,f39,f35])).

fof(f17,plain,
    ( r1_tarski(sK1,u1_pre_topc(sK0))
    | v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:10:41 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.44  % (20837)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.20/0.47  % (20839)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.20/0.48  % (20839)Refutation not found, incomplete strategy% (20839)------------------------------
% 0.20/0.48  % (20839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (20839)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (20839)Memory used [KB]: 5373
% 0.20/0.48  % (20839)Time elapsed: 0.007 s
% 0.20/0.48  % (20839)------------------------------
% 0.20/0.48  % (20839)------------------------------
% 0.20/0.48  % (20829)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.48  % (20829)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f191,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f42,f44,f127,f160,f167,f190])).
% 0.20/0.48  fof(f190,plain,(
% 0.20/0.48    spl4_1 | ~spl4_2),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f189])).
% 0.20/0.48  fof(f189,plain,(
% 0.20/0.48    $false | (spl4_1 | ~spl4_2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f188,f179])).
% 0.20/0.48  fof(f179,plain,(
% 0.20/0.48    ~v3_pre_topc(sK2(sK0,sK1),sK0) | spl4_1),
% 0.20/0.48    inference(subsumption_resolution,[],[f74,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ~v1_tops_2(sK1,sK0) | spl4_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    spl4_1 <=> v1_tops_2(sK1,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    ~v3_pre_topc(sK2(sK0,sK1),sK0) | v1_tops_2(sK1,sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f72,f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    l1_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : ((v1_tops_2(X1,X0) <~> r1_tarski(X1,u1_pre_topc(X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,negated_conjecture,(
% 0.20/0.48    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 0.20/0.48    inference(negated_conjecture,[],[f7])).
% 0.20/0.48  fof(f7,conjecture,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tops_2)).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | ~v3_pre_topc(sK2(sK0,sK1),sK0) | v1_tops_2(sK1,sK0)),
% 0.20/0.48    inference(resolution,[],[f27,f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_pre_topc(sK2(X0,X1),X0) | v1_tops_2(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(flattening,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v3_pre_topc(X2,X0))))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).
% 0.20/0.48  fof(f188,plain,(
% 0.20/0.48    v3_pre_topc(sK2(sK0,sK1),sK0) | (spl4_1 | ~spl4_2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f187,f175])).
% 0.20/0.48  fof(f175,plain,(
% 0.20/0.48    r2_hidden(sK2(sK0,sK1),u1_pre_topc(sK0)) | (spl4_1 | ~spl4_2)),
% 0.20/0.48    inference(resolution,[],[f174,f172])).
% 0.20/0.48  fof(f172,plain,(
% 0.20/0.48    ( ! [X2] : (~r2_hidden(X2,sK1) | r2_hidden(X2,u1_pre_topc(sK0))) ) | ~spl4_2),
% 0.20/0.48    inference(resolution,[],[f169,f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.48  fof(f169,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_pre_topc(sK0))) | ~spl4_2),
% 0.20/0.48    inference(resolution,[],[f41,f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    r1_tarski(sK1,u1_pre_topc(sK0)) | ~spl4_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    spl4_2 <=> r1_tarski(sK1,u1_pre_topc(sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.48  fof(f174,plain,(
% 0.20/0.48    r2_hidden(sK2(sK0,sK1),sK1) | spl4_1),
% 0.20/0.48    inference(subsumption_resolution,[],[f57,f36])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    r2_hidden(sK2(sK0,sK1),sK1) | v1_tops_2(sK1,sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f55,f20])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | r2_hidden(sK2(sK0,sK1),sK1) | v1_tops_2(sK1,sK0)),
% 0.20/0.48    inference(resolution,[],[f26,f19])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | r2_hidden(sK2(X0,X1),X1) | v1_tops_2(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f187,plain,(
% 0.20/0.48    ~r2_hidden(sK2(sK0,sK1),u1_pre_topc(sK0)) | v3_pre_topc(sK2(sK0,sK1),sK0) | spl4_1),
% 0.20/0.48    inference(subsumption_resolution,[],[f182,f20])).
% 0.20/0.48  fof(f182,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | ~r2_hidden(sK2(sK0,sK1),u1_pre_topc(sK0)) | v3_pre_topc(sK2(sK0,sK1),sK0) | spl4_1),
% 0.20/0.48    inference(resolution,[],[f180,f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.20/0.48  fof(f180,plain,(
% 0.20/0.48    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_1),
% 0.20/0.48    inference(subsumption_resolution,[],[f168,f36])).
% 0.20/0.48  fof(f168,plain,(
% 0.20/0.48    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_2(sK1,sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f130,f20])).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_2(sK1,sK0)),
% 0.20/0.48    inference(resolution,[],[f25,f19])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_tops_2(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f167,plain,(
% 0.20/0.48    spl4_2 | ~spl4_9),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f166])).
% 0.20/0.48  fof(f166,plain,(
% 0.20/0.48    $false | (spl4_2 | ~spl4_9)),
% 0.20/0.48    inference(subsumption_resolution,[],[f165,f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ~r1_tarski(sK1,u1_pre_topc(sK0)) | spl4_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f39])).
% 0.20/0.48  fof(f165,plain,(
% 0.20/0.48    r1_tarski(sK1,u1_pre_topc(sK0)) | ~spl4_9),
% 0.20/0.48    inference(subsumption_resolution,[],[f164,f19])).
% 0.20/0.48  fof(f164,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r1_tarski(sK1,u1_pre_topc(sK0)) | ~spl4_9),
% 0.20/0.48    inference(subsumption_resolution,[],[f161,f48])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.48    inference(resolution,[],[f21,f20])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.20/0.48  fof(f161,plain,(
% 0.20/0.48    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r1_tarski(sK1,u1_pre_topc(sK0)) | ~spl4_9),
% 0.20/0.48    inference(resolution,[],[f126,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(flattening,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    r2_hidden(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),u1_pre_topc(sK0)) | ~spl4_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f124])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    spl4_9 <=> r2_hidden(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),u1_pre_topc(sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.48  fof(f160,plain,(
% 0.20/0.48    ~spl4_1 | spl4_2 | spl4_8),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f159])).
% 0.20/0.48  fof(f159,plain,(
% 0.20/0.48    $false | (~spl4_1 | spl4_2 | spl4_8)),
% 0.20/0.48    inference(subsumption_resolution,[],[f158,f122])).
% 0.20/0.48  fof(f122,plain,(
% 0.20/0.48    ~v3_pre_topc(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),sK0) | spl4_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f120])).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    spl4_8 <=> v3_pre_topc(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.48  fof(f158,plain,(
% 0.20/0.48    v3_pre_topc(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),sK0) | (~spl4_1 | spl4_2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f157,f93])).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    r2_hidden(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),sK1) | spl4_2),
% 0.20/0.48    inference(subsumption_resolution,[],[f92,f40])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    r2_hidden(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),sK1) | r1_tarski(sK1,u1_pre_topc(sK0))),
% 0.20/0.48    inference(resolution,[],[f89,f48])).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0),sK1) | r1_tarski(sK1,X0)) )),
% 0.20/0.48    inference(resolution,[],[f30,f19])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r2_hidden(sK3(X0,X1,X2),X1) | r1_tarski(X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f157,plain,(
% 0.20/0.48    ~r2_hidden(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),sK1) | v3_pre_topc(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),sK0) | (~spl4_1 | spl4_2)),
% 0.20/0.48    inference(resolution,[],[f156,f109])).
% 0.20/0.48  fof(f109,plain,(
% 0.20/0.48    m1_subset_1(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_2),
% 0.20/0.48    inference(subsumption_resolution,[],[f108,f40])).
% 0.20/0.48  fof(f108,plain,(
% 0.20/0.48    m1_subset_1(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,u1_pre_topc(sK0))),
% 0.20/0.48    inference(resolution,[],[f76,f48])).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,X0)) )),
% 0.20/0.48    inference(resolution,[],[f29,f19])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(sK3(X0,X1,X2),X0) | r1_tarski(X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f156,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,sK1) | v3_pre_topc(X0,sK0)) ) | ~spl4_1),
% 0.20/0.48    inference(subsumption_resolution,[],[f155,f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    v1_tops_2(sK1,sK0) | ~spl4_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f35])).
% 0.20/0.48  fof(f155,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,sK1) | v3_pre_topc(X0,sK0) | ~v1_tops_2(sK1,sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f153,f20])).
% 0.20/0.48  fof(f153,plain,(
% 0.20/0.48    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,sK1) | v3_pre_topc(X0,sK0) | ~v1_tops_2(sK1,sK0)) )),
% 0.20/0.48    inference(resolution,[],[f24,f19])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,X1) | v3_pre_topc(X2,X0) | ~v1_tops_2(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    ~spl4_8 | spl4_9 | spl4_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f116,f39,f124,f120])).
% 0.20/0.48  fof(f116,plain,(
% 0.20/0.48    r2_hidden(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),u1_pre_topc(sK0)) | ~v3_pre_topc(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),sK0) | spl4_2),
% 0.20/0.48    inference(subsumption_resolution,[],[f110,f20])).
% 0.20/0.48  fof(f110,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | r2_hidden(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),u1_pre_topc(sK0)) | ~v3_pre_topc(sK3(k1_zfmisc_1(u1_struct_0(sK0)),sK1,u1_pre_topc(sK0)),sK0) | spl4_2),
% 0.20/0.48    inference(resolution,[],[f109,f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ~spl4_1 | ~spl4_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f43,f39,f35])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ~v1_tops_2(sK1,sK0) | ~spl4_2),
% 0.20/0.48    inference(subsumption_resolution,[],[f18,f41])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ~r1_tarski(sK1,u1_pre_topc(sK0)) | ~v1_tops_2(sK1,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    spl4_1 | spl4_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f17,f39,f35])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    r1_tarski(sK1,u1_pre_topc(sK0)) | v1_tops_2(sK1,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (20829)------------------------------
% 0.20/0.48  % (20829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (20829)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (20829)Memory used [KB]: 5373
% 0.20/0.48  % (20829)Time elapsed: 0.007 s
% 0.20/0.48  % (20829)------------------------------
% 0.20/0.48  % (20829)------------------------------
% 0.20/0.48  % (20816)Success in time 0.128 s
%------------------------------------------------------------------------------
