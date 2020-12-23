%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  150 (1727 expanded)
%              Number of leaves         :   20 ( 606 expanded)
%              Depth                    :   27
%              Number of atoms          :  442 (9679 expanded)
%              Number of equality atoms :   78 (1719 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f976,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f482,f969])).

fof(f969,plain,(
    ~ spl4_35 ),
    inference(avatar_contradiction_clause,[],[f968])).

fof(f968,plain,
    ( $false
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f917,f85])).

fof(f85,plain,(
    ! [X1] : ~ v1_subset_1(X1,X1) ),
    inference(subsumption_resolution,[],[f80,f83])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f55,f54])).

fof(f54,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f80,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f917,plain,
    ( v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl4_35 ),
    inference(superposition,[],[f110,f912])).

fof(f912,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK0)
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f911,f908])).

fof(f908,plain,
    ( r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl4_35 ),
    inference(forward_demodulation,[],[f907,f604])).

fof(f604,plain,(
    u1_struct_0(sK0) = u1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f603,f446])).

fof(f446,plain,(
    u1_struct_0(sK0) = k2_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f445,f83])).

fof(f445,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f444,f170])).

fof(f170,plain,(
    u1_struct_0(sK2) = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f157,f169])).

fof(f169,plain,(
    ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f168,f47])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ~ v1_tex_2(sK2,sK0)
    & v1_tex_2(sK1,sK0)
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    & m1_pre_topc(sK2,sK0)
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f36,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tex_2(X2,X0)
                & v1_tex_2(X1,X0)
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X2,X0) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,sK0)
              & v1_tex_2(X1,sK0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,sK0) )
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v1_tex_2(X2,sK0)
            & v1_tex_2(X1,sK0)
            & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
            & m1_pre_topc(X2,sK0) )
        & m1_pre_topc(X1,sK0) )
   => ( ? [X2] :
          ( ~ v1_tex_2(X2,sK0)
          & v1_tex_2(sK1,sK0)
          & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
          & m1_pre_topc(X2,sK0) )
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X2] :
        ( ~ v1_tex_2(X2,sK0)
        & v1_tex_2(sK1,sK0)
        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        & m1_pre_topc(X2,sK0) )
   => ( ~ v1_tex_2(sK2,sK0)
      & v1_tex_2(sK1,sK0)
      & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      & m1_pre_topc(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( ( v1_tex_2(X1,X0)
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                 => v1_tex_2(X2,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( ( v1_tex_2(X1,X0)
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
               => v1_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tex_2)).

fof(f168,plain,
    ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f167,f49])).

fof(f49,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f167,plain,
    ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f161,f52])).

fof(f52,plain,(
    ~ v1_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f161,plain,
    ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))
    | v1_tex_2(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f66,f122])).

fof(f122,plain,(
    u1_struct_0(sK2) = sK3(sK0,sK2) ),
    inference(subsumption_resolution,[],[f121,f47])).

fof(f121,plain,
    ( u1_struct_0(sK2) = sK3(sK0,sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f120,f52])).

fof(f120,plain,
    ( u1_struct_0(sK2) = sK3(sK0,sK2)
    | v1_tex_2(sK2,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f65,f49])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X1) = sK3(X0,X1)
      | v1_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK3(X0,X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK3(X0,X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f157,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK0)
    | v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f102,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f102,plain,(
    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f100,f47])).

fof(f100,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f62,f49])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f444,plain,
    ( u1_struct_0(sK0) = k2_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0)))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f443,f92])).

fof(f92,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f90,f47])).

fof(f90,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f60,f49])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f443,plain,
    ( u1_struct_0(sK0) = k2_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0)))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f436,f234])).

fof(f234,plain,(
    v1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f233,f170])).

fof(f233,plain,(
    v1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK2))) ),
    inference(resolution,[],[f104,f92])).

fof(f104,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | v1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0))) ) ),
    inference(resolution,[],[f72,f83])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f436,plain,
    ( u1_struct_0(sK0) = k2_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0)))
    | ~ v1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f238,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).

fof(f238,plain,(
    m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),sK2) ),
    inference(forward_demodulation,[],[f237,f170])).

fof(f237,plain,(
    m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK2)),sK2) ),
    inference(resolution,[],[f107,f92])).

fof(f107,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0)),X0) ) ),
    inference(resolution,[],[f73,f83])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f603,plain,(
    k2_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0))) = u1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0))) ),
    inference(resolution,[],[f513,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f513,plain,(
    l1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0))) ),
    inference(resolution,[],[f480,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f480,plain,(
    l1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f442,f92])).

fof(f442,plain,
    ( l1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f238,f60])).

fof(f907,plain,
    ( r1_tarski(u1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0))),u1_struct_0(sK1))
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f883,f91])).

fof(f91,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f89,f47])).

fof(f89,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f60,f48])).

fof(f48,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f883,plain,
    ( r1_tarski(u1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ spl4_35 ),
    inference(resolution,[],[f877,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f877,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),sK1)
    | ~ spl4_35 ),
    inference(resolution,[],[f743,f474])).

fof(f474,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2)))
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f472])).

fof(f472,plain,
    ( spl4_35
  <=> m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f743,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2)))
      | m1_pre_topc(X2,sK1) ) ),
    inference(subsumption_resolution,[],[f741,f91])).

fof(f741,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2)))
      | m1_pre_topc(X2,sK1)
      | ~ l1_pre_topc(sK1) ) ),
    inference(superposition,[],[f69,f239])).

fof(f239,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2)) ),
    inference(superposition,[],[f50,f170])).

fof(f50,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f911,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))
    | u1_struct_0(sK1) = u1_struct_0(sK0) ),
    inference(forward_demodulation,[],[f532,f521])).

fof(f521,plain,(
    u1_struct_0(sK1) = u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f520,f269])).

fof(f269,plain,(
    u1_struct_0(sK1) = k2_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f268,f47])).

fof(f268,plain,
    ( u1_struct_0(sK1) = k2_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f267,f101])).

fof(f101,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f99,f47])).

fof(f99,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f62,f48])).

fof(f267,plain,
    ( u1_struct_0(sK1) = k2_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f260,f153])).

fof(f153,plain,(
    v1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f150,f47])).

fof(f150,plain,
    ( v1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f101,f72])).

fof(f260,plain,
    ( u1_struct_0(sK1) = k2_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1)))
    | ~ v1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f152,f79])).

fof(f152,plain,(
    m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK1)),sK0) ),
    inference(subsumption_resolution,[],[f149,f47])).

fof(f149,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK1)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f101,f73])).

fof(f520,plain,(
    k2_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1))) = u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1))) ),
    inference(resolution,[],[f504,f56])).

fof(f504,plain,(
    l1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1))) ),
    inference(resolution,[],[f298,f57])).

fof(f298,plain,(
    l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f266,f47])).

fof(f266,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f152,f60])).

fof(f532,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK0)
    | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f531,f521])).

fof(f531,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1)))
    | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1)))) ),
    inference(resolution,[],[f297,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f297,plain,(
    r1_tarski(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1))),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f265,f47])).

fof(f265,plain,
    ( r1_tarski(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1))),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f152,f61])).

fof(f110,plain,(
    v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f109,f47])).

fof(f109,plain,
    ( v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f108,f48])).

fof(f108,plain,
    ( v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f84,f51])).

fof(f51,plain,(
    v1_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f77,f62])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f482,plain,(
    spl4_35 ),
    inference(avatar_contradiction_clause,[],[f481])).

% (23252)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
fof(f481,plain,
    ( $false
    | spl4_35 ),
    inference(global_subsumption,[],[f466,f480,f473])).

fof(f473,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2)))
    | spl4_35 ),
    inference(avatar_component_clause,[],[f472])).

fof(f466,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f465,f239])).

fof(f465,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f464,f50])).

fof(f464,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f439,f92])).

fof(f439,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0))) ),
    inference(resolution,[],[f238,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:59:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (23258)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.51  % (23254)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (23242)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (23260)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.52  % (23251)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (23264)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (23254)Refutation not found, incomplete strategy% (23254)------------------------------
% 0.22/0.52  % (23254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (23254)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (23254)Memory used [KB]: 6396
% 0.22/0.52  % (23254)Time elapsed: 0.083 s
% 0.22/0.52  % (23254)------------------------------
% 0.22/0.52  % (23254)------------------------------
% 0.22/0.52  % (23255)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (23243)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.52  % (23249)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (23262)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.53  % (23244)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.53  % (23253)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.53  % (23241)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.53  % (23247)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.53  % (23246)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.53  % (23241)Refutation not found, incomplete strategy% (23241)------------------------------
% 0.22/0.53  % (23241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (23241)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (23241)Memory used [KB]: 10618
% 0.22/0.53  % (23241)Time elapsed: 0.115 s
% 0.22/0.53  % (23241)------------------------------
% 0.22/0.53  % (23241)------------------------------
% 0.22/0.53  % (23250)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.53  % (23247)Refutation not found, incomplete strategy% (23247)------------------------------
% 0.22/0.53  % (23247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (23247)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (23247)Memory used [KB]: 10618
% 0.22/0.53  % (23247)Time elapsed: 0.076 s
% 0.22/0.53  % (23247)------------------------------
% 0.22/0.53  % (23247)------------------------------
% 0.22/0.53  % (23246)Refutation not found, incomplete strategy% (23246)------------------------------
% 0.22/0.53  % (23246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (23246)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (23246)Memory used [KB]: 6140
% 0.22/0.53  % (23246)Time elapsed: 0.115 s
% 0.22/0.53  % (23246)------------------------------
% 0.22/0.53  % (23246)------------------------------
% 0.22/0.54  % (23265)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.54  % (23261)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.54  % (23263)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.55  % (23245)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.55  % (23267)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.55  % (23251)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f976,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f482,f969])).
% 0.22/0.55  fof(f969,plain,(
% 0.22/0.55    ~spl4_35),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f968])).
% 0.22/0.55  fof(f968,plain,(
% 0.22/0.55    $false | ~spl4_35),
% 0.22/0.55    inference(subsumption_resolution,[],[f917,f85])).
% 0.22/0.55  fof(f85,plain,(
% 0.22/0.55    ( ! [X1] : (~v1_subset_1(X1,X1)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f80,f83])).
% 0.22/0.55  fof(f83,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.55    inference(forward_demodulation,[],[f55,f54])).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.22/0.55  fof(f80,plain,(
% 0.22/0.55    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 0.22/0.55    inference(equality_resolution,[],[f70])).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f44])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.55    inference(nnf_transformation,[],[f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,axiom,(
% 0.22/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.22/0.55  fof(f917,plain,(
% 0.22/0.55    v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) | ~spl4_35),
% 0.22/0.55    inference(superposition,[],[f110,f912])).
% 0.22/0.55  fof(f912,plain,(
% 0.22/0.55    u1_struct_0(sK1) = u1_struct_0(sK0) | ~spl4_35),
% 0.22/0.55    inference(subsumption_resolution,[],[f911,f908])).
% 0.22/0.55  fof(f908,plain,(
% 0.22/0.55    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl4_35),
% 0.22/0.55    inference(forward_demodulation,[],[f907,f604])).
% 0.22/0.55  fof(f604,plain,(
% 0.22/0.55    u1_struct_0(sK0) = u1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0)))),
% 0.22/0.55    inference(forward_demodulation,[],[f603,f446])).
% 0.22/0.55  fof(f446,plain,(
% 0.22/0.55    u1_struct_0(sK0) = k2_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0)))),
% 0.22/0.55    inference(subsumption_resolution,[],[f445,f83])).
% 0.22/0.55  fof(f445,plain,(
% 0.22/0.55    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0)))),
% 0.22/0.55    inference(forward_demodulation,[],[f444,f170])).
% 0.22/0.55  fof(f170,plain,(
% 0.22/0.55    u1_struct_0(sK2) = u1_struct_0(sK0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f157,f169])).
% 0.22/0.55  fof(f169,plain,(
% 0.22/0.55    ~v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))),
% 0.22/0.55    inference(subsumption_resolution,[],[f168,f47])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    l1_pre_topc(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f37])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ((~v1_tex_2(sK2,sK0) & v1_tex_2(sK1,sK0) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_pre_topc(sK2,sK0)) & m1_pre_topc(sK1,sK0)) & l1_pre_topc(sK0)),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f36,f35,f34])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tex_2(X2,sK0) & v1_tex_2(X1,sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(X1,sK0)) & l1_pre_topc(sK0))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ? [X1] : (? [X2] : (~v1_tex_2(X2,sK0) & v1_tex_2(X1,sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(X1,sK0)) => (? [X2] : (~v1_tex_2(X2,sK0) & v1_tex_2(sK1,sK0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(sK1,sK0))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ? [X2] : (~v1_tex_2(X2,sK0) & v1_tex_2(sK1,sK0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_pre_topc(X2,sK0)) => (~v1_tex_2(sK2,sK0) & v1_tex_2(sK1,sK0) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_pre_topc(sK2,sK0))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.22/0.55    inference(flattening,[],[f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (? [X2] : ((~v1_tex_2(X2,X0) & (v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f17])).
% 0.22/0.55  fof(f17,negated_conjecture,(
% 0.22/0.55    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 0.22/0.55    inference(negated_conjecture,[],[f16])).
% 0.22/0.55  fof(f16,conjecture,(
% 0.22/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tex_2)).
% 0.22/0.55  fof(f168,plain,(
% 0.22/0.55    ~v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f167,f49])).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    m1_pre_topc(sK2,sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f37])).
% 0.22/0.55  fof(f167,plain,(
% 0.22/0.55    ~v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f161,f52])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    ~v1_tex_2(sK2,sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f37])).
% 0.22/0.55  fof(f161,plain,(
% 0.22/0.55    ~v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) | v1_tex_2(sK2,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.55    inference(superposition,[],[f66,f122])).
% 0.22/0.55  fof(f122,plain,(
% 0.22/0.55    u1_struct_0(sK2) = sK3(sK0,sK2)),
% 0.22/0.55    inference(subsumption_resolution,[],[f121,f47])).
% 0.22/0.55  fof(f121,plain,(
% 0.22/0.55    u1_struct_0(sK2) = sK3(sK0,sK2) | ~l1_pre_topc(sK0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f120,f52])).
% 0.22/0.55  fof(f120,plain,(
% 0.22/0.55    u1_struct_0(sK2) = sK3(sK0,sK2) | v1_tex_2(sK2,sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.55    inference(resolution,[],[f65,f49])).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | u1_struct_0(X1) = sK3(X0,X1) | v1_tex_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f42])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.55    inference(rectify,[],[f39])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.55    inference(nnf_transformation,[],[f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.55    inference(flattening,[],[f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f14])).
% 0.22/0.55  fof(f14,axiom,(
% 0.22/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f42])).
% 0.22/0.55  fof(f157,plain,(
% 0.22/0.55    u1_struct_0(sK2) = u1_struct_0(sK0) | v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))),
% 0.22/0.55    inference(resolution,[],[f102,f71])).
% 0.22/0.55  fof(f71,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f44])).
% 0.22/0.55  fof(f102,plain,(
% 0.22/0.55    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.55    inference(subsumption_resolution,[],[f100,f47])).
% 0.22/0.55  fof(f100,plain,(
% 0.22/0.55    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.22/0.55    inference(resolution,[],[f62,f49])).
% 0.22/0.55  fof(f62,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,axiom,(
% 0.22/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.55  fof(f444,plain,(
% 0.22/0.55    u1_struct_0(sK0) = k2_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.22/0.55    inference(subsumption_resolution,[],[f443,f92])).
% 0.22/0.55  fof(f92,plain,(
% 0.22/0.55    l1_pre_topc(sK2)),
% 0.22/0.55    inference(subsumption_resolution,[],[f90,f47])).
% 0.22/0.55  fof(f90,plain,(
% 0.22/0.55    l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 0.22/0.55    inference(resolution,[],[f60,f49])).
% 0.22/0.55  fof(f60,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,axiom,(
% 0.22/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.55  fof(f443,plain,(
% 0.22/0.55    u1_struct_0(sK0) = k2_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 0.22/0.55    inference(subsumption_resolution,[],[f436,f234])).
% 0.22/0.55  fof(f234,plain,(
% 0.22/0.55    v1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)))),
% 0.22/0.55    inference(forward_demodulation,[],[f233,f170])).
% 0.22/0.55  fof(f233,plain,(
% 0.22/0.55    v1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK2)))),
% 0.22/0.55    inference(resolution,[],[f104,f92])).
% 0.22/0.55  fof(f104,plain,(
% 0.22/0.55    ( ! [X0] : (~l1_pre_topc(X0) | v1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0)))) )),
% 0.22/0.55    inference(resolution,[],[f72,f83])).
% 0.22/0.55  fof(f72,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_pre_topc(k1_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f33])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.55    inference(flattening,[],[f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.22/0.55  fof(f436,plain,(
% 0.22/0.55    u1_struct_0(sK0) = k2_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0))) | ~v1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 0.22/0.55    inference(resolution,[],[f238,f79])).
% 0.22/0.55  fof(f79,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_pre_topc(k1_pre_topc(X0,X1),X0) | k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.55    inference(equality_resolution,[],[f67])).
% 0.22/0.55  fof(f67,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f43])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : (((k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1) & (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.55    inference(nnf_transformation,[],[f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.55    inference(flattening,[],[f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).
% 0.22/0.55  fof(f238,plain,(
% 0.22/0.55    m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),sK2)),
% 0.22/0.55    inference(forward_demodulation,[],[f237,f170])).
% 0.22/0.55  fof(f237,plain,(
% 0.22/0.55    m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK2)),sK2)),
% 0.22/0.55    inference(resolution,[],[f107,f92])).
% 0.22/0.55  fof(f107,plain,(
% 0.22/0.55    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0)),X0)) )),
% 0.22/0.55    inference(resolution,[],[f73,f83])).
% 0.22/0.55  fof(f73,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f33])).
% 0.22/0.55  fof(f603,plain,(
% 0.22/0.55    k2_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0))) = u1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0)))),
% 0.22/0.55    inference(resolution,[],[f513,f56])).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f20])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.55  fof(f513,plain,(
% 0.22/0.55    l1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0)))),
% 0.22/0.55    inference(resolution,[],[f480,f57])).
% 0.22/0.55  fof(f57,plain,(
% 0.22/0.55    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.55  fof(f480,plain,(
% 0.22/0.55    l1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)))),
% 0.22/0.55    inference(subsumption_resolution,[],[f442,f92])).
% 0.22/0.55  fof(f442,plain,(
% 0.22/0.55    l1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0))) | ~l1_pre_topc(sK2)),
% 0.22/0.55    inference(resolution,[],[f238,f60])).
% 0.22/0.55  fof(f907,plain,(
% 0.22/0.55    r1_tarski(u1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0))),u1_struct_0(sK1)) | ~spl4_35),
% 0.22/0.55    inference(subsumption_resolution,[],[f883,f91])).
% 0.22/0.55  fof(f91,plain,(
% 0.22/0.55    l1_pre_topc(sK1)),
% 0.22/0.55    inference(subsumption_resolution,[],[f89,f47])).
% 0.22/0.55  fof(f89,plain,(
% 0.22/0.55    l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.55    inference(resolution,[],[f60,f48])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    m1_pre_topc(sK1,sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f37])).
% 0.22/0.55  fof(f883,plain,(
% 0.22/0.55    r1_tarski(u1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~spl4_35),
% 0.22/0.55    inference(resolution,[],[f877,f61])).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,axiom,(
% 0.22/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.22/0.55  fof(f877,plain,(
% 0.22/0.55    m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),sK1) | ~spl4_35),
% 0.22/0.55    inference(resolution,[],[f743,f474])).
% 0.22/0.55  fof(f474,plain,(
% 0.22/0.55    m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2))) | ~spl4_35),
% 0.22/0.55    inference(avatar_component_clause,[],[f472])).
% 0.22/0.55  fof(f472,plain,(
% 0.22/0.55    spl4_35 <=> m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.22/0.55  fof(f743,plain,(
% 0.22/0.55    ( ! [X2] : (~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2))) | m1_pre_topc(X2,sK1)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f741,f91])).
% 0.22/0.55  fof(f741,plain,(
% 0.22/0.55    ( ! [X2] : (~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2))) | m1_pre_topc(X2,sK1) | ~l1_pre_topc(sK1)) )),
% 0.22/0.55    inference(superposition,[],[f69,f239])).
% 0.22/0.55  fof(f239,plain,(
% 0.22/0.55    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2))),
% 0.22/0.55    inference(superposition,[],[f50,f170])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.22/0.55    inference(cnf_transformation,[],[f37])).
% 0.22/0.55  fof(f69,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,axiom,(
% 0.22/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).
% 0.22/0.55  fof(f911,plain,(
% 0.22/0.55    ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) | u1_struct_0(sK1) = u1_struct_0(sK0)),
% 0.22/0.55    inference(forward_demodulation,[],[f532,f521])).
% 0.22/0.55  fof(f521,plain,(
% 0.22/0.55    u1_struct_0(sK1) = u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1)))),
% 0.22/0.55    inference(forward_demodulation,[],[f520,f269])).
% 0.22/0.55  fof(f269,plain,(
% 0.22/0.55    u1_struct_0(sK1) = k2_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1)))),
% 0.22/0.55    inference(subsumption_resolution,[],[f268,f47])).
% 0.22/0.55  fof(f268,plain,(
% 0.22/0.55    u1_struct_0(sK1) = k2_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(sK0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f267,f101])).
% 0.22/0.55  fof(f101,plain,(
% 0.22/0.55    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.55    inference(subsumption_resolution,[],[f99,f47])).
% 0.22/0.55  fof(f99,plain,(
% 0.22/0.55    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.22/0.55    inference(resolution,[],[f62,f48])).
% 0.22/0.55  fof(f267,plain,(
% 0.22/0.55    u1_struct_0(sK1) = k2_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f260,f153])).
% 0.22/0.55  fof(f153,plain,(
% 0.22/0.55    v1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK1)))),
% 0.22/0.55    inference(subsumption_resolution,[],[f150,f47])).
% 0.22/0.55  fof(f150,plain,(
% 0.22/0.55    v1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(sK0)),
% 0.22/0.55    inference(resolution,[],[f101,f72])).
% 0.22/0.55  fof(f260,plain,(
% 0.22/0.55    u1_struct_0(sK1) = k2_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1))) | ~v1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK1))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.22/0.55    inference(resolution,[],[f152,f79])).
% 0.22/0.55  fof(f152,plain,(
% 0.22/0.55    m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK1)),sK0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f149,f47])).
% 0.22/0.55  fof(f149,plain,(
% 0.22/0.55    m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK1)),sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.55    inference(resolution,[],[f101,f73])).
% 0.22/0.55  fof(f520,plain,(
% 0.22/0.55    k2_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1))) = u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1)))),
% 0.22/0.55    inference(resolution,[],[f504,f56])).
% 0.22/0.55  fof(f504,plain,(
% 0.22/0.55    l1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1)))),
% 0.22/0.55    inference(resolution,[],[f298,f57])).
% 0.22/0.55  fof(f298,plain,(
% 0.22/0.55    l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK1)))),
% 0.22/0.55    inference(subsumption_resolution,[],[f266,f47])).
% 0.22/0.55  fof(f266,plain,(
% 0.22/0.55    l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(sK0)),
% 0.22/0.55    inference(resolution,[],[f152,f60])).
% 0.22/0.55  fof(f532,plain,(
% 0.22/0.55    u1_struct_0(sK1) = u1_struct_0(sK0) | ~r1_tarski(u1_struct_0(sK0),u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1))))),
% 0.22/0.55    inference(forward_demodulation,[],[f531,f521])).
% 0.22/0.55  fof(f531,plain,(
% 0.22/0.55    u1_struct_0(sK0) = u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1))) | ~r1_tarski(u1_struct_0(sK0),u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1))))),
% 0.22/0.55    inference(resolution,[],[f297,f76])).
% 0.22/0.55  fof(f76,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f46])).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.55    inference(flattening,[],[f45])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.55    inference(nnf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.55  fof(f297,plain,(
% 0.22/0.55    r1_tarski(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1))),u1_struct_0(sK0))),
% 0.22/0.55    inference(subsumption_resolution,[],[f265,f47])).
% 0.22/0.55  fof(f265,plain,(
% 0.22/0.55    r1_tarski(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK1))),u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 0.22/0.55    inference(resolution,[],[f152,f61])).
% 0.22/0.55  fof(f110,plain,(
% 0.22/0.55    v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.22/0.55    inference(subsumption_resolution,[],[f109,f47])).
% 0.22/0.55  fof(f109,plain,(
% 0.22/0.55    v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f108,f48])).
% 0.22/0.55  fof(f108,plain,(
% 0.22/0.55    v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.55    inference(resolution,[],[f84,f51])).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    v1_tex_2(sK1,sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f37])).
% 0.22/0.55  fof(f84,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f77,f62])).
% 0.22/0.55  fof(f77,plain,(
% 0.22/0.55    ( ! [X0,X1] : (v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.55    inference(equality_resolution,[],[f63])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f42])).
% 0.22/0.55  fof(f482,plain,(
% 0.22/0.55    spl4_35),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f481])).
% 0.22/0.55  % (23252)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.55  fof(f481,plain,(
% 0.22/0.55    $false | spl4_35),
% 0.22/0.55    inference(global_subsumption,[],[f466,f480,f473])).
% 0.22/0.55  fof(f473,plain,(
% 0.22/0.55    ~m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2))) | spl4_35),
% 0.22/0.55    inference(avatar_component_clause,[],[f472])).
% 0.22/0.55  fof(f466,plain,(
% 0.22/0.55    m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2))) | ~l1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)))),
% 0.22/0.55    inference(forward_demodulation,[],[f465,f239])).
% 0.22/0.55  fof(f465,plain,(
% 0.22/0.55    m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)))),
% 0.22/0.55    inference(forward_demodulation,[],[f464,f50])).
% 0.22/0.55  fof(f464,plain,(
% 0.22/0.55    m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)))),
% 0.22/0.55    inference(subsumption_resolution,[],[f439,f92])).
% 0.22/0.55  fof(f439,plain,(
% 0.22/0.55    m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(sK2) | ~l1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK0)))),
% 0.22/0.55    inference(resolution,[],[f238,f58])).
% 0.22/0.55  fof(f58,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f38])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.55    inference(nnf_transformation,[],[f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,axiom,(
% 0.22/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (23251)------------------------------
% 0.22/0.55  % (23251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (23251)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (23251)Memory used [KB]: 11129
% 0.22/0.55  % (23251)Time elapsed: 0.136 s
% 0.22/0.55  % (23251)------------------------------
% 0.22/0.55  % (23251)------------------------------
% 0.22/0.55  % (23248)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.56  % (23266)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.56  % (23256)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.54/0.57  % (23257)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.54/0.57  % (23240)Success in time 0.196 s
%------------------------------------------------------------------------------
