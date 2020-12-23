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
% DateTime   : Thu Dec  3 13:17:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 927 expanded)
%              Number of leaves         :   16 ( 354 expanded)
%              Depth                    :   23
%              Number of atoms          :  401 (9326 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f144,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f65,f110,f114,f134,f143])).

fof(f143,plain,
    ( ~ spl4_1
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | ~ spl4_1
    | spl4_4 ),
    inference(subsumption_resolution,[],[f141,f74])).

fof(f74,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f71,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f71,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f67,f29])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( r1_tsep_1(sK3,sK2)
      | r1_tsep_1(sK2,sK3) )
    & ( ~ r1_tsep_1(sK3,sK1)
      | ~ r1_tsep_1(sK1,sK3) )
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f23,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X2,X3) )
                    & ( ~ r1_tsep_1(X3,X1)
                      | ~ r1_tsep_1(X1,X3) )
                    & m1_pre_topc(X1,X2)
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X2,X3) )
                & ( ~ r1_tsep_1(X3,X1)
                  | ~ r1_tsep_1(X1,X3) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( r1_tsep_1(X3,X2)
                | r1_tsep_1(X2,X3) )
              & ( ~ r1_tsep_1(X3,sK1)
                | ~ r1_tsep_1(sK1,X3) )
              & m1_pre_topc(sK1,X2)
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( r1_tsep_1(X3,X2)
              | r1_tsep_1(X2,X3) )
            & ( ~ r1_tsep_1(X3,sK1)
              | ~ r1_tsep_1(sK1,X3) )
            & m1_pre_topc(sK1,X2)
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( r1_tsep_1(X3,sK2)
            | r1_tsep_1(sK2,X3) )
          & ( ~ r1_tsep_1(X3,sK1)
            | ~ r1_tsep_1(sK1,X3) )
          & m1_pre_topc(sK1,sK2)
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X3] :
        ( ( r1_tsep_1(X3,sK2)
          | r1_tsep_1(sK2,X3) )
        & ( ~ r1_tsep_1(X3,sK1)
          | ~ r1_tsep_1(sK1,X3) )
        & m1_pre_topc(sK1,sK2)
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ( r1_tsep_1(sK3,sK2)
        | r1_tsep_1(sK2,sK3) )
      & ( ~ r1_tsep_1(sK3,sK1)
        | ~ r1_tsep_1(sK1,sK3) )
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tmap_1)).

fof(f67,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f42,f31])).

fof(f31,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f141,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl4_1
    | spl4_4 ),
    inference(subsumption_resolution,[],[f140,f76])).

fof(f76,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f73,f41])).

fof(f73,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f69,f29])).

fof(f69,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f42,f35])).

fof(f35,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f140,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | ~ spl4_1
    | spl4_4 ),
    inference(subsumption_resolution,[],[f137,f64])).

fof(f64,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl4_4
  <=> r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f137,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f135,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f135,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f131,f74])).

fof(f131,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ l1_struct_0(sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f127,f36])).

fof(f36,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f127,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | r1_tsep_1(X0,sK3)
        | ~ l1_struct_0(X0) )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f125,f76])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | r1_tsep_1(X0,sK3)
        | ~ l1_struct_0(sK3)
        | ~ l1_struct_0(X0) )
    | ~ spl4_1 ),
    inference(resolution,[],[f118,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f118,plain,
    ( ! [X0] :
        ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK3))
        | ~ m1_pre_topc(X0,sK2) )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f117,f72])).

fof(f72,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f68,f29])).

fof(f68,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f42,f33])).

fof(f33,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f117,plain,
    ( ! [X0] :
        ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK3))
        | ~ l1_pre_topc(sK2)
        | ~ m1_pre_topc(X0,sK2) )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f115,f76])).

fof(f115,plain,
    ( ! [X0] :
        ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK3))
        | ~ l1_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ m1_pre_topc(X0,sK2) )
    | ~ spl4_1 ),
    inference(resolution,[],[f51,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X1,X0)
      | r1_xboole_0(u1_struct_0(X2),u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X1) ) ),
    inference(subsumption_resolution,[],[f86,f41])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ l1_struct_0(X1)
      | r1_xboole_0(u1_struct_0(X2),u1_struct_0(X0))
      | ~ r1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X1) ) ),
    inference(resolution,[],[f83,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(resolution,[],[f43,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,u1_struct_0(X0))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | r1_xboole_0(X2,u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1) ) ),
    inference(resolution,[],[f39,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl4_1
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f134,plain,
    ( ~ spl4_1
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | ~ spl4_1
    | spl4_3 ),
    inference(subsumption_resolution,[],[f132,f74])).

fof(f132,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl4_1
    | spl4_3 ),
    inference(subsumption_resolution,[],[f131,f60])).

fof(f60,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl4_3
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f114,plain,
    ( ~ spl4_2
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | ~ spl4_2
    | spl4_3 ),
    inference(subsumption_resolution,[],[f60,f101])).

fof(f101,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f100,f74])).

fof(f100,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ l1_struct_0(sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f99,f36])).

fof(f99,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | r1_tsep_1(X0,sK3)
        | ~ l1_struct_0(X0) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f97,f76])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | r1_tsep_1(X0,sK3)
        | ~ l1_struct_0(sK3)
        | ~ l1_struct_0(X0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f93,f40])).

fof(f93,plain,
    ( ! [X1] :
        ( r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK3))
        | ~ m1_pre_topc(X1,sK2) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f92,f72])).

fof(f92,plain,
    ( ! [X1] :
        ( r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK3))
        | ~ l1_pre_topc(sK2)
        | ~ m1_pre_topc(X1,sK2) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f89,f76])).

fof(f89,plain,
    ( ! [X1] :
        ( r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK3))
        | ~ l1_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ m1_pre_topc(X1,sK2) )
    | ~ spl4_2 ),
    inference(resolution,[],[f87,f80])).

fof(f80,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f79,f76])).

fof(f79,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_struct_0(sK3)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f78,f75])).

fof(f75,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f72,f41])).

fof(f78,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f44,f55])).

fof(f55,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl4_2
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f110,plain,
    ( ~ spl4_2
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | ~ spl4_2
    | spl4_4 ),
    inference(subsumption_resolution,[],[f108,f74])).

fof(f108,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl4_2
    | spl4_4 ),
    inference(subsumption_resolution,[],[f107,f76])).

fof(f107,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | ~ spl4_2
    | spl4_4 ),
    inference(subsumption_resolution,[],[f104,f64])).

fof(f104,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f101,f44])).

fof(f65,plain,
    ( ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f37,f62,f58])).

fof(f37,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f38,f53,f49])).

fof(f38,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:22:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.44  % (20729)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.20/0.44  % (20729)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f144,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f56,f65,f110,f114,f134,f143])).
% 0.20/0.45  fof(f143,plain,(
% 0.20/0.45    ~spl4_1 | spl4_4),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f142])).
% 0.20/0.45  fof(f142,plain,(
% 0.20/0.45    $false | (~spl4_1 | spl4_4)),
% 0.20/0.45    inference(subsumption_resolution,[],[f141,f74])).
% 0.20/0.45  fof(f74,plain,(
% 0.20/0.45    l1_struct_0(sK1)),
% 0.20/0.45    inference(resolution,[],[f71,f41])).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f13])).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.45  fof(f71,plain,(
% 0.20/0.45    l1_pre_topc(sK1)),
% 0.20/0.45    inference(subsumption_resolution,[],[f67,f29])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    l1_pre_topc(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f24])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ((((r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)) & (~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f23,f22,f21,f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : ((r1_tsep_1(X3,sK2) | r1_tsep_1(sK2,X3)) & (~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ? [X3] : ((r1_tsep_1(X3,sK2) | r1_tsep_1(sK2,X3)) & (~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => ((r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)) & (~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f10])).
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3))) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f9])).
% 0.20/0.45  fof(f9,negated_conjecture,(
% 0.20/0.45    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.20/0.45    inference(negated_conjecture,[],[f8])).
% 0.20/0.45  fof(f8,conjecture,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tmap_1)).
% 0.20/0.45  fof(f67,plain,(
% 0.20/0.45    l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.20/0.45    inference(resolution,[],[f42,f31])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    m1_pre_topc(sK1,sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f24])).
% 0.20/0.45  fof(f42,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f14])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.45  fof(f141,plain,(
% 0.20/0.45    ~l1_struct_0(sK1) | (~spl4_1 | spl4_4)),
% 0.20/0.45    inference(subsumption_resolution,[],[f140,f76])).
% 0.20/0.45  fof(f76,plain,(
% 0.20/0.45    l1_struct_0(sK3)),
% 0.20/0.45    inference(resolution,[],[f73,f41])).
% 0.20/0.45  fof(f73,plain,(
% 0.20/0.45    l1_pre_topc(sK3)),
% 0.20/0.45    inference(subsumption_resolution,[],[f69,f29])).
% 0.20/0.45  fof(f69,plain,(
% 0.20/0.45    l1_pre_topc(sK3) | ~l1_pre_topc(sK0)),
% 0.20/0.45    inference(resolution,[],[f42,f35])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    m1_pre_topc(sK3,sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f24])).
% 0.20/0.45  fof(f140,plain,(
% 0.20/0.45    ~l1_struct_0(sK3) | ~l1_struct_0(sK1) | (~spl4_1 | spl4_4)),
% 0.20/0.45    inference(subsumption_resolution,[],[f137,f64])).
% 0.20/0.45  fof(f64,plain,(
% 0.20/0.45    ~r1_tsep_1(sK3,sK1) | spl4_4),
% 0.20/0.45    inference(avatar_component_clause,[],[f62])).
% 0.20/0.45  fof(f62,plain,(
% 0.20/0.45    spl4_4 <=> r1_tsep_1(sK3,sK1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.45  fof(f137,plain,(
% 0.20/0.45    r1_tsep_1(sK3,sK1) | ~l1_struct_0(sK3) | ~l1_struct_0(sK1) | ~spl4_1),
% 0.20/0.45    inference(resolution,[],[f135,f44])).
% 0.20/0.45  fof(f44,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f17])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f16])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 0.20/0.45  fof(f135,plain,(
% 0.20/0.45    r1_tsep_1(sK1,sK3) | ~spl4_1),
% 0.20/0.45    inference(subsumption_resolution,[],[f131,f74])).
% 0.20/0.45  fof(f131,plain,(
% 0.20/0.45    r1_tsep_1(sK1,sK3) | ~l1_struct_0(sK1) | ~spl4_1),
% 0.20/0.45    inference(resolution,[],[f127,f36])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    m1_pre_topc(sK1,sK2)),
% 0.20/0.45    inference(cnf_transformation,[],[f24])).
% 0.20/0.45  fof(f127,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_pre_topc(X0,sK2) | r1_tsep_1(X0,sK3) | ~l1_struct_0(X0)) ) | ~spl4_1),
% 0.20/0.45    inference(subsumption_resolution,[],[f125,f76])).
% 0.20/0.45  fof(f125,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_pre_topc(X0,sK2) | r1_tsep_1(X0,sK3) | ~l1_struct_0(sK3) | ~l1_struct_0(X0)) ) | ~spl4_1),
% 0.20/0.45    inference(resolution,[],[f118,f40])).
% 0.20/0.45  fof(f40,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f25])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.20/0.45    inference(nnf_transformation,[],[f12])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).
% 0.20/0.45  fof(f118,plain,(
% 0.20/0.45    ( ! [X0] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK3)) | ~m1_pre_topc(X0,sK2)) ) | ~spl4_1),
% 0.20/0.45    inference(subsumption_resolution,[],[f117,f72])).
% 0.20/0.45  fof(f72,plain,(
% 0.20/0.45    l1_pre_topc(sK2)),
% 0.20/0.45    inference(subsumption_resolution,[],[f68,f29])).
% 0.20/0.45  fof(f68,plain,(
% 0.20/0.45    l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 0.20/0.45    inference(resolution,[],[f42,f33])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    m1_pre_topc(sK2,sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f24])).
% 0.20/0.45  fof(f117,plain,(
% 0.20/0.45    ( ! [X0] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK3)) | ~l1_pre_topc(sK2) | ~m1_pre_topc(X0,sK2)) ) | ~spl4_1),
% 0.20/0.45    inference(subsumption_resolution,[],[f115,f76])).
% 0.20/0.45  fof(f115,plain,(
% 0.20/0.45    ( ! [X0] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK3)) | ~l1_struct_0(sK3) | ~l1_pre_topc(sK2) | ~m1_pre_topc(X0,sK2)) ) | ~spl4_1),
% 0.20/0.45    inference(resolution,[],[f51,f87])).
% 0.20/0.45  fof(f87,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r1_tsep_1(X1,X0) | r1_xboole_0(u1_struct_0(X2),u1_struct_0(X0)) | ~l1_struct_0(X0) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X1)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f86,f41])).
% 0.20/0.45  fof(f86,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~l1_struct_0(X1) | r1_xboole_0(u1_struct_0(X2),u1_struct_0(X0)) | ~r1_tsep_1(X1,X0) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X1)) )),
% 0.20/0.45    inference(resolution,[],[f83,f82])).
% 0.20/0.45  fof(f82,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1)) )),
% 0.20/0.45    inference(resolution,[],[f43,f45])).
% 0.20/0.45  fof(f45,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f26])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.45    inference(nnf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.45  fof(f43,plain,(
% 0.20/0.45    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f15])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f7])).
% 0.20/0.45  fof(f7,axiom,(
% 0.20/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.45  fof(f83,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X2,u1_struct_0(X0)) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | r1_xboole_0(X2,u1_struct_0(X1)) | ~r1_tsep_1(X0,X1)) )),
% 0.20/0.45    inference(resolution,[],[f39,f47])).
% 0.20/0.45  fof(f47,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.45    inference(flattening,[],[f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.45    inference(ennf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f25])).
% 0.20/0.45  fof(f51,plain,(
% 0.20/0.45    r1_tsep_1(sK2,sK3) | ~spl4_1),
% 0.20/0.45    inference(avatar_component_clause,[],[f49])).
% 0.20/0.45  fof(f49,plain,(
% 0.20/0.45    spl4_1 <=> r1_tsep_1(sK2,sK3)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.45  fof(f134,plain,(
% 0.20/0.45    ~spl4_1 | spl4_3),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f133])).
% 0.20/0.45  fof(f133,plain,(
% 0.20/0.45    $false | (~spl4_1 | spl4_3)),
% 0.20/0.45    inference(subsumption_resolution,[],[f132,f74])).
% 0.20/0.45  fof(f132,plain,(
% 0.20/0.45    ~l1_struct_0(sK1) | (~spl4_1 | spl4_3)),
% 0.20/0.45    inference(subsumption_resolution,[],[f131,f60])).
% 0.20/0.45  fof(f60,plain,(
% 0.20/0.45    ~r1_tsep_1(sK1,sK3) | spl4_3),
% 0.20/0.45    inference(avatar_component_clause,[],[f58])).
% 0.20/0.45  fof(f58,plain,(
% 0.20/0.45    spl4_3 <=> r1_tsep_1(sK1,sK3)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.45  fof(f114,plain,(
% 0.20/0.45    ~spl4_2 | spl4_3),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f113])).
% 0.20/0.45  fof(f113,plain,(
% 0.20/0.45    $false | (~spl4_2 | spl4_3)),
% 0.20/0.45    inference(subsumption_resolution,[],[f60,f101])).
% 0.20/0.45  fof(f101,plain,(
% 0.20/0.45    r1_tsep_1(sK1,sK3) | ~spl4_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f100,f74])).
% 0.20/0.45  fof(f100,plain,(
% 0.20/0.45    r1_tsep_1(sK1,sK3) | ~l1_struct_0(sK1) | ~spl4_2),
% 0.20/0.45    inference(resolution,[],[f99,f36])).
% 0.20/0.45  fof(f99,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_pre_topc(X0,sK2) | r1_tsep_1(X0,sK3) | ~l1_struct_0(X0)) ) | ~spl4_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f97,f76])).
% 0.20/0.45  fof(f97,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_pre_topc(X0,sK2) | r1_tsep_1(X0,sK3) | ~l1_struct_0(sK3) | ~l1_struct_0(X0)) ) | ~spl4_2),
% 0.20/0.45    inference(resolution,[],[f93,f40])).
% 0.20/0.45  fof(f93,plain,(
% 0.20/0.45    ( ! [X1] : (r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK3)) | ~m1_pre_topc(X1,sK2)) ) | ~spl4_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f92,f72])).
% 0.20/0.45  fof(f92,plain,(
% 0.20/0.45    ( ! [X1] : (r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK3)) | ~l1_pre_topc(sK2) | ~m1_pre_topc(X1,sK2)) ) | ~spl4_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f89,f76])).
% 0.20/0.45  fof(f89,plain,(
% 0.20/0.45    ( ! [X1] : (r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK3)) | ~l1_struct_0(sK3) | ~l1_pre_topc(sK2) | ~m1_pre_topc(X1,sK2)) ) | ~spl4_2),
% 0.20/0.45    inference(resolution,[],[f87,f80])).
% 0.20/0.45  fof(f80,plain,(
% 0.20/0.45    r1_tsep_1(sK2,sK3) | ~spl4_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f79,f76])).
% 0.20/0.45  fof(f79,plain,(
% 0.20/0.45    r1_tsep_1(sK2,sK3) | ~l1_struct_0(sK3) | ~spl4_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f78,f75])).
% 0.20/0.45  fof(f75,plain,(
% 0.20/0.45    l1_struct_0(sK2)),
% 0.20/0.45    inference(resolution,[],[f72,f41])).
% 0.20/0.45  fof(f78,plain,(
% 0.20/0.45    r1_tsep_1(sK2,sK3) | ~l1_struct_0(sK2) | ~l1_struct_0(sK3) | ~spl4_2),
% 0.20/0.45    inference(resolution,[],[f44,f55])).
% 0.20/0.45  fof(f55,plain,(
% 0.20/0.45    r1_tsep_1(sK3,sK2) | ~spl4_2),
% 0.20/0.45    inference(avatar_component_clause,[],[f53])).
% 0.20/0.45  fof(f53,plain,(
% 0.20/0.45    spl4_2 <=> r1_tsep_1(sK3,sK2)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.45  fof(f110,plain,(
% 0.20/0.45    ~spl4_2 | spl4_4),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f109])).
% 0.20/0.45  fof(f109,plain,(
% 0.20/0.45    $false | (~spl4_2 | spl4_4)),
% 0.20/0.45    inference(subsumption_resolution,[],[f108,f74])).
% 0.20/0.45  fof(f108,plain,(
% 0.20/0.45    ~l1_struct_0(sK1) | (~spl4_2 | spl4_4)),
% 0.20/0.45    inference(subsumption_resolution,[],[f107,f76])).
% 0.20/0.45  fof(f107,plain,(
% 0.20/0.45    ~l1_struct_0(sK3) | ~l1_struct_0(sK1) | (~spl4_2 | spl4_4)),
% 0.20/0.45    inference(subsumption_resolution,[],[f104,f64])).
% 0.20/0.45  fof(f104,plain,(
% 0.20/0.45    r1_tsep_1(sK3,sK1) | ~l1_struct_0(sK3) | ~l1_struct_0(sK1) | ~spl4_2),
% 0.20/0.45    inference(resolution,[],[f101,f44])).
% 0.20/0.45  fof(f65,plain,(
% 0.20/0.45    ~spl4_3 | ~spl4_4),
% 0.20/0.45    inference(avatar_split_clause,[],[f37,f62,f58])).
% 0.20/0.45  fof(f37,plain,(
% 0.20/0.45    ~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)),
% 0.20/0.45    inference(cnf_transformation,[],[f24])).
% 0.20/0.45  fof(f56,plain,(
% 0.20/0.45    spl4_1 | spl4_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f38,f53,f49])).
% 0.20/0.45  fof(f38,plain,(
% 0.20/0.45    r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)),
% 0.20/0.45    inference(cnf_transformation,[],[f24])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (20729)------------------------------
% 0.20/0.45  % (20729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (20729)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (20729)Memory used [KB]: 5373
% 0.20/0.45  % (20729)Time elapsed: 0.039 s
% 0.20/0.45  % (20729)------------------------------
% 0.20/0.45  % (20729)------------------------------
% 0.20/0.45  % (20709)Success in time 0.096 s
%------------------------------------------------------------------------------
