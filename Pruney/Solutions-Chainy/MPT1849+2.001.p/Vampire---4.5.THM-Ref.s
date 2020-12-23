%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  192 (6025 expanded)
%              Number of leaves         :   24 (1690 expanded)
%              Depth                    :   31
%              Number of atoms          :  512 (27264 expanded)
%              Number of equality atoms :   99 (6188 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1304,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f199,f233,f465,f617,f1303])).

fof(f1303,plain,
    ( ~ spl3_9
    | ~ spl3_31 ),
    inference(avatar_contradiction_clause,[],[f1302])).

fof(f1302,plain,
    ( $false
    | ~ spl3_9
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f1301,f1199])).

fof(f1199,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k1_pre_topc(sK1,u1_struct_0(sK0))
    | ~ spl3_9
    | ~ spl3_31 ),
    inference(superposition,[],[f324,f1118])).

fof(f1118,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(sK1,u1_struct_0(sK0))
    | ~ spl3_9
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f1117,f464])).

fof(f464,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f462])).

fof(f462,plain,
    ( spl3_31
  <=> u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f1117,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(sK1,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))))
    | ~ spl3_9
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f1116,f93])).

fof(f93,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f59,f58])).

fof(f58,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f1116,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(sK1,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))))
    | ~ spl3_9
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f1115,f464])).

fof(f1115,plain,
    ( ~ m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(sK1,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))))
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f1114,f269])).

fof(f269,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f237,f252])).

fof(f252,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))))
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f198,f209])).

fof(f209,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f205,f203])).

fof(f203,plain,(
    ~ v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f202,f54])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & m1_pre_topc(sK1,sK0)
    & ~ v1_tex_2(sK1,sK0)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & m1_pre_topc(X1,X0)
            & ~ v1_tex_2(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
          & m1_pre_topc(X1,sK0)
          & ~ v1_tex_2(X1,sK0) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        & m1_pre_topc(X1,sK0)
        & ~ v1_tex_2(X1,sK0) )
   => ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      & m1_pre_topc(sK1,sK0)
      & ~ v1_tex_2(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & m1_pre_topc(X1,X0)
          & ~ v1_tex_2(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & m1_pre_topc(X1,X0)
          & ~ v1_tex_2(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v1_tex_2(X1,X0) )
           => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v1_tex_2(X1,X0) )
           => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v1_tex_2(X1,X0) )
         => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tex_2)).

fof(f202,plain,
    ( ~ v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f201,f56])).

fof(f56,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f201,plain,
    ( ~ v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f200,f55])).

fof(f55,plain,(
    ~ v1_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f200,plain,
    ( ~ v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | v1_tex_2(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f74,f130])).

fof(f130,plain,(
    u1_struct_0(sK1) = sK2(sK0,sK1) ),
    inference(subsumption_resolution,[],[f129,f54])).

fof(f129,plain,
    ( u1_struct_0(sK1) = sK2(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f127,f55])).

fof(f127,plain,
    ( u1_struct_0(sK1) = sK2(sK0,sK1)
    | v1_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f73,f56])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | v1_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK2(X0,X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f47,f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK2(X0,X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v1_subset_1(X2,u1_struct_0(X0))
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f205,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f145,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f145,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f144,f130])).

fof(f144,plain,(
    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f143,f54])).

fof(f143,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f141,f55])).

fof(f141,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f72,f56])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f198,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl3_9
  <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f237,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))))) ),
    inference(forward_demodulation,[],[f236,f209])).

fof(f236,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    inference(subsumption_resolution,[],[f227,f54])).

fof(f227,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f114,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f114,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) ),
    inference(subsumption_resolution,[],[f113,f54])).

fof(f113,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f70,f56])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1114,plain,
    ( ~ m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(sK1,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))))
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f1112,f669])).

fof(f669,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)),sK1)
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f668,f252])).

fof(f668,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))),sK1) ),
    inference(forward_demodulation,[],[f667,f209])).

fof(f667,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK1) ),
    inference(subsumption_resolution,[],[f656,f99])).

fof(f99,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f98,f54])).

fof(f98,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f67,f56])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f656,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f158,f70])).

fof(f158,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) ),
    inference(subsumption_resolution,[],[f153,f99])).

fof(f153,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f100,f70])).

fof(f100,plain,(
    m1_pre_topc(sK1,sK1) ),
    inference(resolution,[],[f99,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f1112,plain,
    ( ~ m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)),sK1)
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(sK1,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))) ),
    inference(superposition,[],[f339,f536])).

fof(f536,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))) = k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))) ),
    inference(resolution,[],[f364,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f364,plain,(
    l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))) ),
    inference(resolution,[],[f247,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f247,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))) ),
    inference(forward_demodulation,[],[f246,f209])).

fof(f246,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f225,f54])).

fof(f225,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f114,f67])).

fof(f339,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_pre_topc(X0,sK1)
      | ~ v1_pre_topc(X0)
      | k1_pre_topc(sK1,k2_struct_0(X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f331,f99])).

fof(f331,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_pre_topc(X0,sK1)
      | ~ v1_pre_topc(X0)
      | k1_pre_topc(sK1,k2_struct_0(X0)) = X0
      | ~ l1_pre_topc(sK1) ) ),
    inference(superposition,[],[f88,f209])).

fof(f88,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | k1_pre_topc(X0,k2_struct_0(X2)) = X2
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_pre_topc(X0,X1) = X2
      | k2_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_pre_topc(X0,X1) = X2
                  | k2_struct_0(X2) != X1 )
                & ( k2_struct_0(X2) = X1
                  | k1_pre_topc(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

fof(f324,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) ),
    inference(superposition,[],[f57,f209])).

fof(f57,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f1301,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k1_pre_topc(sK1,u1_struct_0(sK0))
    | ~ spl3_9
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f1300,f1296])).

fof(f1296,plain,
    ( k1_pre_topc(sK1,u1_struct_0(sK0)) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),u1_struct_0(sK0))
    | ~ spl3_9
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f1295,f1118])).

fof(f1295,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),u1_struct_0(sK0))
    | ~ spl3_9
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f1294,f464])).

fof(f1294,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))))
    | ~ spl3_9
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f1293,f536])).

fof(f1293,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))))
    | ~ spl3_9
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f1292,f93])).

fof(f1292,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))))
    | ~ spl3_9
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f1291,f464])).

fof(f1291,plain,
    ( ~ m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))))
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f1290,f536])).

fof(f1290,plain,
    ( ~ m1_subset_1(k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))))
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f1288,f269])).

fof(f1288,plain,
    ( ~ m1_subset_1(k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))) ),
    inference(resolution,[],[f722,f251])).

fof(f251,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f250,f247])).

fof(f250,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(forward_demodulation,[],[f249,f209])).

fof(f249,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(forward_demodulation,[],[f248,f209])).

fof(f248,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f224,f54])).

fof(f224,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(resolution,[],[f114,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f722,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_pre_topc(X0)
      | k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k2_struct_0(X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f716,f212])).

fof(f212,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f102,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f102,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f63,f54])).

fof(f63,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f716,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ v1_pre_topc(X0)
      | k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k2_struct_0(X0)) = X0
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ) ),
    inference(superposition,[],[f88,f472])).

fof(f472,plain,(
    u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f471,f394])).

fof(f394,plain,(
    r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f389,f54])).

fof(f389,plain,
    ( r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f119,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f119,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f115,f54])).

fof(f115,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f96,f70])).

fof(f96,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(resolution,[],[f62,f54])).

fof(f471,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0)) ),
    inference(resolution,[],[f282,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f282,plain,(
    r1_tarski(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(forward_demodulation,[],[f281,f209])).

fof(f281,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(subsumption_resolution,[],[f274,f212])).

fof(f274,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f125,f68])).

fof(f125,plain,(
    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f124,f99])).

fof(f124,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f121,f54])).

fof(f121,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f65,f56])).

fof(f1300,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f1299,f511])).

fof(f511,plain,(
    u1_struct_0(sK0) = k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(forward_demodulation,[],[f510,f472])).

fof(f510,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f350,f60])).

fof(f350,plain,(
    l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f212,f61])).

fof(f1299,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(subsumption_resolution,[],[f1298,f93])).

fof(f1298,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(forward_demodulation,[],[f1297,f511])).

fof(f1297,plain,
    ( ~ m1_subset_1(k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(subsumption_resolution,[],[f1289,f120])).

fof(f120,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f116,f54])).

fof(f116,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f96,f69])).

fof(f1289,plain,
    ( ~ m1_subset_1(k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(resolution,[],[f722,f349])).

fof(f349,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f212,f62])).

fof(f617,plain,(
    spl3_30 ),
    inference(avatar_contradiction_clause,[],[f616])).

fof(f616,plain,
    ( $false
    | spl3_30 ),
    inference(subsumption_resolution,[],[f615,f247])).

fof(f615,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))
    | spl3_30 ),
    inference(forward_demodulation,[],[f614,f209])).

fof(f614,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl3_30 ),
    inference(subsumption_resolution,[],[f613,f460])).

fof(f460,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))))
    | spl3_30 ),
    inference(avatar_component_clause,[],[f458])).

fof(f458,plain,
    ( spl3_30
  <=> r1_tarski(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f613,plain,
    ( r1_tarski(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(forward_demodulation,[],[f601,f209])).

fof(f601,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(resolution,[],[f157,f68])).

fof(f157,plain,(
    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f156,f99])).

fof(f156,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(duplicate_literal_removal,[],[f149])).

fof(f149,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f100,f65])).

fof(f465,plain,
    ( ~ spl3_30
    | spl3_31 ),
    inference(avatar_split_clause,[],[f456,f462,f458])).

fof(f456,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))
    | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))) ),
    inference(resolution,[],[f235,f86])).

fof(f235,plain,(
    r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f234,f209])).

fof(f234,plain,(
    r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f226,f54])).

fof(f226,plain,
    ( r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f114,f68])).

fof(f233,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | spl3_8 ),
    inference(subsumption_resolution,[],[f231,f54])).

fof(f231,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_8 ),
    inference(subsumption_resolution,[],[f225,f194])).

fof(f194,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl3_8
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f199,plain,
    ( ~ spl3_8
    | spl3_9 ),
    inference(avatar_split_clause,[],[f190,f196,f192])).

fof(f190,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(resolution,[],[f112,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f112,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f111,f54])).

fof(f111,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f69,f56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:34:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (28688)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.48  % (28685)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.49  % (28679)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.49  % (28696)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.50  % (28680)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (28681)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (28684)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (28687)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (28686)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (28689)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (28691)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (28683)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (28682)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (28692)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (28700)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (28694)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (28698)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (28693)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (28699)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (28695)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (28697)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (28702)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.53  % (28678)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.53  % (28701)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % (28691)Refutation not found, incomplete strategy% (28691)------------------------------
% 0.21/0.53  % (28691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (28690)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (28678)Refutation not found, incomplete strategy% (28678)------------------------------
% 0.21/0.53  % (28678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28678)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (28678)Memory used [KB]: 10618
% 0.21/0.54  % (28678)Time elapsed: 0.090 s
% 0.21/0.54  % (28678)------------------------------
% 0.21/0.54  % (28678)------------------------------
% 0.21/0.54  % (28688)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (28703)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.54  % (28691)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (28691)Memory used [KB]: 6396
% 0.21/0.54  % (28691)Time elapsed: 0.105 s
% 0.21/0.54  % (28691)------------------------------
% 0.21/0.54  % (28691)------------------------------
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f1304,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f199,f233,f465,f617,f1303])).
% 0.21/0.55  fof(f1303,plain,(
% 0.21/0.55    ~spl3_9 | ~spl3_31),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f1302])).
% 0.21/0.55  fof(f1302,plain,(
% 0.21/0.55    $false | (~spl3_9 | ~spl3_31)),
% 0.21/0.55    inference(subsumption_resolution,[],[f1301,f1199])).
% 0.21/0.55  fof(f1199,plain,(
% 0.21/0.55    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k1_pre_topc(sK1,u1_struct_0(sK0)) | (~spl3_9 | ~spl3_31)),
% 0.21/0.55    inference(superposition,[],[f324,f1118])).
% 0.21/0.55  fof(f1118,plain,(
% 0.21/0.55    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(sK1,u1_struct_0(sK0)) | (~spl3_9 | ~spl3_31)),
% 0.21/0.55    inference(forward_demodulation,[],[f1117,f464])).
% 0.21/0.55  fof(f464,plain,(
% 0.21/0.55    u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))) | ~spl3_31),
% 0.21/0.55    inference(avatar_component_clause,[],[f462])).
% 0.21/0.55  fof(f462,plain,(
% 0.21/0.55    spl3_31 <=> u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.55  fof(f1117,plain,(
% 0.21/0.55    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(sK1,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))) | (~spl3_9 | ~spl3_31)),
% 0.21/0.55    inference(subsumption_resolution,[],[f1116,f93])).
% 0.21/0.55  fof(f93,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f59,f58])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.55  fof(f1116,plain,(
% 0.21/0.55    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(sK1,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))) | (~spl3_9 | ~spl3_31)),
% 0.21/0.55    inference(forward_demodulation,[],[f1115,f464])).
% 0.21/0.55  fof(f1115,plain,(
% 0.21/0.55    ~m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(sK1,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))) | ~spl3_9),
% 0.21/0.55    inference(subsumption_resolution,[],[f1114,f269])).
% 0.21/0.55  fof(f269,plain,(
% 0.21/0.55    v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))) | ~spl3_9),
% 0.21/0.55    inference(forward_demodulation,[],[f237,f252])).
% 0.21/0.55  fof(f252,plain,(
% 0.21/0.55    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))) | ~spl3_9),
% 0.21/0.55    inference(forward_demodulation,[],[f198,f209])).
% 0.21/0.55  fof(f209,plain,(
% 0.21/0.55    u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f205,f203])).
% 0.21/0.55  fof(f203,plain,(
% 0.21/0.55    ~v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.55    inference(subsumption_resolution,[],[f202,f54])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    l1_pre_topc(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f44])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_pre_topc(sK1,sK0) & ~v1_tex_2(sK1,sK0)) & l1_pre_topc(sK0)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f43,f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & m1_pre_topc(X1,sK0) & ~v1_tex_2(X1,sK0)) & l1_pre_topc(sK0))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ? [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & m1_pre_topc(X1,sK0) & ~v1_tex_2(X1,sK0)) => (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_pre_topc(sK1,sK0) & ~v1_tex_2(sK1,sK0))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0)) & l1_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & (m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0))) & l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0)) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 0.21/0.55    inference(pure_predicate_removal,[],[f20])).
% 0.21/0.55  fof(f20,negated_conjecture,(
% 0.21/0.55    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0)) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 0.21/0.55    inference(negated_conjecture,[],[f19])).
% 0.21/0.55  fof(f19,conjecture,(
% 0.21/0.55    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0)) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tex_2)).
% 0.21/0.55  fof(f202,plain,(
% 0.21/0.55    ~v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f201,f56])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    m1_pre_topc(sK1,sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f44])).
% 0.21/0.55  fof(f201,plain,(
% 0.21/0.55    ~v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f200,f55])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ~v1_tex_2(sK1,sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f44])).
% 0.21/0.55  fof(f200,plain,(
% 0.21/0.55    ~v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) | v1_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.55    inference(superposition,[],[f74,f130])).
% 0.21/0.55  fof(f130,plain,(
% 0.21/0.55    u1_struct_0(sK1) = sK2(sK0,sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f129,f54])).
% 0.21/0.55  fof(f129,plain,(
% 0.21/0.55    u1_struct_0(sK1) = sK2(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f127,f55])).
% 0.21/0.55  fof(f127,plain,(
% 0.21/0.55    u1_struct_0(sK1) = sK2(sK0,sK1) | v1_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.55    inference(resolution,[],[f73,f56])).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | u1_struct_0(X1) = sK2(X0,X1) | v1_tex_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f49])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f47,f48])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(rectify,[],[f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f49])).
% 0.21/0.55  fof(f205,plain,(
% 0.21/0.55    u1_struct_0(sK0) = u1_struct_0(sK1) | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.55    inference(resolution,[],[f145,f79])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f51])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(nnf_transformation,[],[f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.21/0.55  fof(f145,plain,(
% 0.21/0.55    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    inference(forward_demodulation,[],[f144,f130])).
% 0.21/0.55  fof(f144,plain,(
% 0.21/0.55    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    inference(subsumption_resolution,[],[f143,f54])).
% 0.21/0.55  fof(f143,plain,(
% 0.21/0.55    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f141,f55])).
% 0.21/0.55  fof(f141,plain,(
% 0.21/0.55    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.55    inference(resolution,[],[f72,f56])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_tex_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f49])).
% 0.21/0.55  fof(f198,plain,(
% 0.21/0.55    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl3_9),
% 0.21/0.55    inference(avatar_component_clause,[],[f196])).
% 0.21/0.55  fof(f196,plain,(
% 0.21/0.55    spl3_9 <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.55  fof(f237,plain,(
% 0.21/0.55    v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))))),
% 0.21/0.55    inference(forward_demodulation,[],[f236,f209])).
% 0.21/0.55  fof(f236,plain,(
% 0.21/0.55    v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 0.21/0.55    inference(subsumption_resolution,[],[f227,f54])).
% 0.21/0.55  fof(f227,plain,(
% 0.21/0.55    v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~l1_pre_topc(sK0)),
% 0.21/0.55    inference(resolution,[],[f114,f69])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).
% 0.21/0.55  fof(f114,plain,(
% 0.21/0.55    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f113,f54])).
% 0.21/0.55  fof(f113,plain,(
% 0.21/0.55    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.55    inference(resolution,[],[f70,f56])).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f1114,plain,(
% 0.21/0.55    ~m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(sK1,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))) | ~spl3_9),
% 0.21/0.55    inference(subsumption_resolution,[],[f1112,f669])).
% 0.21/0.55  fof(f669,plain,(
% 0.21/0.55    m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)),sK1) | ~spl3_9),
% 0.21/0.55    inference(forward_demodulation,[],[f668,f252])).
% 0.21/0.55  fof(f668,plain,(
% 0.21/0.55    m1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))),sK1)),
% 0.21/0.55    inference(forward_demodulation,[],[f667,f209])).
% 0.21/0.55  fof(f667,plain,(
% 0.21/0.55    m1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f656,f99])).
% 0.21/0.55  fof(f99,plain,(
% 0.21/0.55    l1_pre_topc(sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f98,f54])).
% 0.21/0.55  fof(f98,plain,(
% 0.21/0.55    l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.21/0.55    inference(resolution,[],[f67,f56])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.55  fof(f656,plain,(
% 0.21/0.55    m1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK1) | ~l1_pre_topc(sK1)),
% 0.21/0.55    inference(resolution,[],[f158,f70])).
% 0.21/0.55  fof(f158,plain,(
% 0.21/0.55    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f153,f99])).
% 0.21/0.55  fof(f153,plain,(
% 0.21/0.55    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) | ~l1_pre_topc(sK1)),
% 0.21/0.55    inference(resolution,[],[f100,f70])).
% 0.21/0.55  fof(f100,plain,(
% 0.21/0.55    m1_pre_topc(sK1,sK1)),
% 0.21/0.55    inference(resolution,[],[f99,f62])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.21/0.55  fof(f1112,plain,(
% 0.21/0.55    ~m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)),sK1) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(sK1,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))))),
% 0.21/0.55    inference(superposition,[],[f339,f536])).
% 0.21/0.55  fof(f536,plain,(
% 0.21/0.55    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))) = k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))),
% 0.21/0.55    inference(resolution,[],[f364,f60])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.55  fof(f364,plain,(
% 0.21/0.55    l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))),
% 0.21/0.55    inference(resolution,[],[f247,f61])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.55  fof(f247,plain,(
% 0.21/0.55    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))),
% 0.21/0.55    inference(forward_demodulation,[],[f246,f209])).
% 0.21/0.55  fof(f246,plain,(
% 0.21/0.55    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.21/0.55    inference(subsumption_resolution,[],[f225,f54])).
% 0.21/0.55  fof(f225,plain,(
% 0.21/0.55    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0)),
% 0.21/0.55    inference(resolution,[],[f114,f67])).
% 0.21/0.55  fof(f339,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(X0,sK1) | ~v1_pre_topc(X0) | k1_pre_topc(sK1,k2_struct_0(X0)) = X0) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f331,f99])).
% 0.21/0.55  fof(f331,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(X0,sK1) | ~v1_pre_topc(X0) | k1_pre_topc(sK1,k2_struct_0(X0)) = X0 | ~l1_pre_topc(sK1)) )),
% 0.21/0.55    inference(superposition,[],[f88,f209])).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    ( ! [X2,X0] : (~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | k1_pre_topc(X0,k2_struct_0(X2)) = X2 | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(equality_resolution,[],[f76])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f50])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (((k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1) & (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).
% 0.21/0.55  fof(f324,plain,(
% 0.21/0.55    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))),
% 0.21/0.55    inference(superposition,[],[f57,f209])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.21/0.55    inference(cnf_transformation,[],[f44])).
% 0.21/0.55  fof(f1301,plain,(
% 0.21/0.55    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k1_pre_topc(sK1,u1_struct_0(sK0)) | (~spl3_9 | ~spl3_31)),
% 0.21/0.55    inference(forward_demodulation,[],[f1300,f1296])).
% 0.21/0.55  fof(f1296,plain,(
% 0.21/0.55    k1_pre_topc(sK1,u1_struct_0(sK0)) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),u1_struct_0(sK0)) | (~spl3_9 | ~spl3_31)),
% 0.21/0.55    inference(forward_demodulation,[],[f1295,f1118])).
% 0.21/0.55  fof(f1295,plain,(
% 0.21/0.55    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),u1_struct_0(sK0)) | (~spl3_9 | ~spl3_31)),
% 0.21/0.55    inference(forward_demodulation,[],[f1294,f464])).
% 0.21/0.55  fof(f1294,plain,(
% 0.21/0.55    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))) | (~spl3_9 | ~spl3_31)),
% 0.21/0.55    inference(forward_demodulation,[],[f1293,f536])).
% 0.21/0.55  fof(f1293,plain,(
% 0.21/0.55    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))) | (~spl3_9 | ~spl3_31)),
% 0.21/0.55    inference(subsumption_resolution,[],[f1292,f93])).
% 0.21/0.55  fof(f1292,plain,(
% 0.21/0.55    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))) | (~spl3_9 | ~spl3_31)),
% 0.21/0.55    inference(forward_demodulation,[],[f1291,f464])).
% 0.21/0.55  fof(f1291,plain,(
% 0.21/0.55    ~m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))) | ~spl3_9),
% 0.21/0.55    inference(forward_demodulation,[],[f1290,f536])).
% 0.21/0.55  fof(f1290,plain,(
% 0.21/0.55    ~m1_subset_1(k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))) | ~spl3_9),
% 0.21/0.55    inference(subsumption_resolution,[],[f1288,f269])).
% 0.21/0.55  fof(f1288,plain,(
% 0.21/0.55    ~m1_subset_1(k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))))),
% 0.21/0.55    inference(resolution,[],[f722,f251])).
% 0.21/0.55  fof(f251,plain,(
% 0.21/0.55    m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.55    inference(subsumption_resolution,[],[f250,f247])).
% 0.21/0.55  fof(f250,plain,(
% 0.21/0.55    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))) | m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.55    inference(forward_demodulation,[],[f249,f209])).
% 0.21/0.55  fof(f249,plain,(
% 0.21/0.55    m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.21/0.55    inference(forward_demodulation,[],[f248,f209])).
% 0.21/0.55  fof(f248,plain,(
% 0.21/0.55    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.21/0.55    inference(subsumption_resolution,[],[f224,f54])).
% 0.21/0.55  fof(f224,plain,(
% 0.21/0.55    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.21/0.55    inference(resolution,[],[f114,f65])).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f45])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.21/0.55  fof(f722,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_pre_topc(X0) | k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k2_struct_0(X0)) = X0) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f716,f212])).
% 0.21/0.55  fof(f212,plain,(
% 0.21/0.55    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.55    inference(resolution,[],[f102,f81])).
% 0.21/0.55  fof(f81,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f40])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 0.21/0.55  fof(f102,plain,(
% 0.21/0.55    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.55    inference(resolution,[],[f63,f54])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.21/0.55  fof(f716,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v1_pre_topc(X0) | k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k2_struct_0(X0)) = X0 | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )),
% 0.21/0.55    inference(superposition,[],[f88,f472])).
% 0.21/0.55  fof(f472,plain,(
% 0.21/0.55    u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.55    inference(subsumption_resolution,[],[f471,f394])).
% 0.21/0.55  fof(f394,plain,(
% 0.21/0.55    r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))),
% 0.21/0.55    inference(subsumption_resolution,[],[f389,f54])).
% 0.21/0.55  fof(f389,plain,(
% 0.21/0.55    r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 0.21/0.55    inference(resolution,[],[f119,f68])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.21/0.55  fof(f119,plain,(
% 0.21/0.55    m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f115,f54])).
% 0.21/0.55  fof(f115,plain,(
% 0.21/0.55    m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.55    inference(resolution,[],[f96,f70])).
% 0.21/0.55  fof(f96,plain,(
% 0.21/0.55    m1_pre_topc(sK0,sK0)),
% 0.21/0.55    inference(resolution,[],[f62,f54])).
% 0.21/0.55  fof(f471,plain,(
% 0.21/0.55    u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))),
% 0.21/0.55    inference(resolution,[],[f282,f86])).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f53])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.55    inference(flattening,[],[f52])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.55    inference(nnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.55  fof(f282,plain,(
% 0.21/0.55    r1_tarski(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 0.21/0.55    inference(forward_demodulation,[],[f281,f209])).
% 0.21/0.55  fof(f281,plain,(
% 0.21/0.55    r1_tarski(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 0.21/0.55    inference(subsumption_resolution,[],[f274,f212])).
% 0.21/0.55  fof(f274,plain,(
% 0.21/0.55    r1_tarski(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.55    inference(resolution,[],[f125,f68])).
% 0.21/0.55  fof(f125,plain,(
% 0.21/0.55    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.55    inference(subsumption_resolution,[],[f124,f99])).
% 0.21/0.55  fof(f124,plain,(
% 0.21/0.55    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f121,f54])).
% 0.21/0.55  fof(f121,plain,(
% 0.21/0.55    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1)),
% 0.21/0.55    inference(resolution,[],[f65,f56])).
% 0.21/0.55  fof(f1300,plain,(
% 0.21/0.55    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),u1_struct_0(sK0))),
% 0.21/0.55    inference(forward_demodulation,[],[f1299,f511])).
% 0.21/0.55  fof(f511,plain,(
% 0.21/0.55    u1_struct_0(sK0) = k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.55    inference(forward_demodulation,[],[f510,f472])).
% 0.21/0.55  fof(f510,plain,(
% 0.21/0.55    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.55    inference(resolution,[],[f350,f60])).
% 0.21/0.55  fof(f350,plain,(
% 0.21/0.55    l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.55    inference(resolution,[],[f212,f61])).
% 0.21/0.55  fof(f1299,plain,(
% 0.21/0.55    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 0.21/0.55    inference(subsumption_resolution,[],[f1298,f93])).
% 0.21/0.55  fof(f1298,plain,(
% 0.21/0.55    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 0.21/0.55    inference(forward_demodulation,[],[f1297,f511])).
% 0.21/0.55  fof(f1297,plain,(
% 0.21/0.55    ~m1_subset_1(k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 0.21/0.55    inference(subsumption_resolution,[],[f1289,f120])).
% 0.21/0.55  fof(f120,plain,(
% 0.21/0.55    v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.55    inference(subsumption_resolution,[],[f116,f54])).
% 0.21/0.55  fof(f116,plain,(
% 0.21/0.55    v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0)),
% 0.21/0.55    inference(resolution,[],[f96,f69])).
% 0.21/0.55  fof(f1289,plain,(
% 0.21/0.55    ~m1_subset_1(k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 0.21/0.55    inference(resolution,[],[f722,f349])).
% 0.21/0.55  fof(f349,plain,(
% 0.21/0.55    m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.55    inference(resolution,[],[f212,f62])).
% 0.21/0.55  fof(f617,plain,(
% 0.21/0.55    spl3_30),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f616])).
% 0.21/0.55  fof(f616,plain,(
% 0.21/0.55    $false | spl3_30),
% 0.21/0.55    inference(subsumption_resolution,[],[f615,f247])).
% 0.21/0.55  fof(f615,plain,(
% 0.21/0.55    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))) | spl3_30),
% 0.21/0.55    inference(forward_demodulation,[],[f614,f209])).
% 0.21/0.55  fof(f614,plain,(
% 0.21/0.55    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl3_30),
% 0.21/0.55    inference(subsumption_resolution,[],[f613,f460])).
% 0.21/0.55  fof(f460,plain,(
% 0.21/0.55    ~r1_tarski(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))) | spl3_30),
% 0.21/0.55    inference(avatar_component_clause,[],[f458])).
% 0.21/0.55  fof(f458,plain,(
% 0.21/0.55    spl3_30 <=> r1_tarski(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.55  fof(f613,plain,(
% 0.21/0.55    r1_tarski(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.21/0.55    inference(forward_demodulation,[],[f601,f209])).
% 0.21/0.55  fof(f601,plain,(
% 0.21/0.55    r1_tarski(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.21/0.55    inference(resolution,[],[f157,f68])).
% 0.21/0.55  fof(f157,plain,(
% 0.21/0.55    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.21/0.55    inference(subsumption_resolution,[],[f156,f99])).
% 0.21/0.55  fof(f156,plain,(
% 0.21/0.55    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1)),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f149])).
% 0.21/0.55  fof(f149,plain,(
% 0.21/0.55    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK1)),
% 0.21/0.55    inference(resolution,[],[f100,f65])).
% 0.21/0.55  fof(f465,plain,(
% 0.21/0.55    ~spl3_30 | spl3_31),
% 0.21/0.55    inference(avatar_split_clause,[],[f456,f462,f458])).
% 0.21/0.55  fof(f456,plain,(
% 0.21/0.55    u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))) | ~r1_tarski(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))))),
% 0.21/0.55    inference(resolution,[],[f235,f86])).
% 0.21/0.55  fof(f235,plain,(
% 0.21/0.55    r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))),u1_struct_0(sK0))),
% 0.21/0.55    inference(forward_demodulation,[],[f234,f209])).
% 0.21/0.55  fof(f234,plain,(
% 0.21/0.55    r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK0))),
% 0.21/0.55    inference(subsumption_resolution,[],[f226,f54])).
% 0.21/0.55  fof(f226,plain,(
% 0.21/0.55    r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 0.21/0.55    inference(resolution,[],[f114,f68])).
% 0.21/0.55  fof(f233,plain,(
% 0.21/0.55    spl3_8),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f232])).
% 0.21/0.55  fof(f232,plain,(
% 0.21/0.55    $false | spl3_8),
% 0.21/0.55    inference(subsumption_resolution,[],[f231,f54])).
% 0.21/0.55  fof(f231,plain,(
% 0.21/0.55    ~l1_pre_topc(sK0) | spl3_8),
% 0.21/0.55    inference(subsumption_resolution,[],[f225,f194])).
% 0.21/0.55  fof(f194,plain,(
% 0.21/0.55    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl3_8),
% 0.21/0.55    inference(avatar_component_clause,[],[f192])).
% 0.21/0.55  fof(f192,plain,(
% 0.21/0.55    spl3_8 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.55  fof(f199,plain,(
% 0.21/0.55    ~spl3_8 | spl3_9),
% 0.21/0.55    inference(avatar_split_clause,[],[f190,f196,f192])).
% 0.21/0.55  fof(f190,plain,(
% 0.21/0.55    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.21/0.55    inference(resolution,[],[f112,f64])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.21/0.55  fof(f112,plain,(
% 0.21/0.55    v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.21/0.55    inference(subsumption_resolution,[],[f111,f54])).
% 0.21/0.55  fof(f111,plain,(
% 0.21/0.55    v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0)),
% 0.21/0.55    inference(resolution,[],[f69,f56])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (28688)------------------------------
% 0.21/0.55  % (28688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (28688)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (28688)Memory used [KB]: 11257
% 0.21/0.55  % (28688)Time elapsed: 0.124 s
% 0.21/0.55  % (28688)------------------------------
% 0.21/0.55  % (28688)------------------------------
% 0.21/0.55  % (28677)Success in time 0.187 s
%------------------------------------------------------------------------------
