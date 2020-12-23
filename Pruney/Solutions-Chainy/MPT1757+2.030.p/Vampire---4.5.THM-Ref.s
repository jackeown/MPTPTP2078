%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 344 expanded)
%              Number of leaves         :   11 (  59 expanded)
%              Depth                    :   51
%              Number of atoms          :  792 (4033 expanded)
%              Number of equality atoms :   17 ( 209 expanded)
%              Maximal formula depth    :   28 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f324,plain,(
    $false ),
    inference(subsumption_resolution,[],[f323,f212])).

fof(f212,plain,(
    ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f211,f178])).

fof(f178,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f165,f47])).

fof(f47,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X1)
                      & v1_tsep_1(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ( X4 = X5
                             => ( r1_tmap_1(X1,X0,X2,X4)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & v1_tsep_1(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( X4 = X5
                           => ( r1_tmap_1(X1,X0,X2,X4)
                            <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).

fof(f165,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f41,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f41,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f211,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f73,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f73,plain,
    ( ~ l1_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[],[f39,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f39,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f323,plain,(
    v1_xboole_0(u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f322,f70])).

fof(f70,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f36,f37])).

fof(f37,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f322,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[],[f321,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f321,plain,(
    ~ r2_hidden(sK4,u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f319,f178])).

fof(f319,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f318,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f318,plain,
    ( ~ m1_pre_topc(sK3,sK3)
    | ~ r2_hidden(sK4,u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f317,f41])).

fof(f317,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ r2_hidden(sK4,u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f315,f47])).

fof(f315,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ r2_hidden(sK4,u1_struct_0(sK3)) ),
    inference(resolution,[],[f314,f46])).

fof(f46,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f314,plain,(
    ! [X2] :
      ( ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ m1_pre_topc(sK3,X2)
      | ~ m1_pre_topc(sK3,sK3)
      | ~ r2_hidden(sK4,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f313,f41])).

fof(f313,plain,(
    ! [X2] :
      ( ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ m1_pre_topc(sK3,X2)
      | ~ m1_pre_topc(sK3,sK3)
      | ~ r2_hidden(sK4,u1_struct_0(sK3))
      | ~ m1_pre_topc(sK3,sK1) ) ),
    inference(subsumption_resolution,[],[f312,f179])).

fof(f179,plain,(
    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f166,f47])).

fof(f166,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f41,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f312,plain,(
    ! [X2] :
      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ m1_pre_topc(sK3,X2)
      | ~ m1_pre_topc(sK3,sK3)
      | ~ r2_hidden(sK4,u1_struct_0(sK3))
      | ~ m1_pre_topc(sK3,sK1) ) ),
    inference(duplicate_literal_removal,[],[f311])).

fof(f311,plain,(
    ! [X2] :
      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ m1_pre_topc(sK3,X2)
      | ~ m1_pre_topc(sK3,X2)
      | ~ m1_pre_topc(sK3,sK3)
      | ~ r2_hidden(sK4,u1_struct_0(sK3))
      | ~ m1_pre_topc(sK3,sK1) ) ),
    inference(resolution,[],[f309,f40])).

fof(f40,plain,(
    v1_tsep_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f309,plain,(
    ! [X0,X1] :
      ( ~ v1_tsep_1(X0,sK1)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK3,X1)
      | ~ m1_pre_topc(X0,sK3)
      | ~ r2_hidden(sK4,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f308,f47])).

fof(f308,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4,u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK3,X1)
      | ~ m1_pre_topc(X0,sK3)
      | ~ l1_pre_topc(sK1)
      | ~ v1_tsep_1(X0,sK1)
      | ~ m1_pre_topc(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f307,f46])).

fof(f307,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4,u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK3,X1)
      | ~ m1_pre_topc(X0,sK3)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_tsep_1(X0,sK1)
      | ~ m1_pre_topc(X0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f306])).

fof(f306,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4,u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK3,X1)
      | ~ m1_pre_topc(X0,sK3)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v1_tsep_1(X0,sK1)
      | ~ m1_pre_topc(X0,sK1) ) ),
    inference(resolution,[],[f304,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v3_pre_topc(X2,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f304,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(u1_struct_0(X0),sK1)
      | ~ r2_hidden(sK4,u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK3,X1)
      | ~ m1_pre_topc(X0,sK3) ) ),
    inference(resolution,[],[f290,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f290,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK3))
      | ~ v3_pre_topc(X0,sK1)
      | ~ r2_hidden(sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(subsumption_resolution,[],[f289,f70])).

fof(f289,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
      | ~ v3_pre_topc(X0,sK1)
      | ~ r2_hidden(sK4,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f288,f38])).

fof(f38,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f288,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
      | ~ v3_pre_topc(X0,sK1)
      | ~ r2_hidden(sK4,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f287,f41])).

fof(f287,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK3,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
      | ~ v3_pre_topc(X0,sK1)
      | ~ r2_hidden(sK4,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f286,f39])).

fof(f286,plain,(
    ! [X0] :
      ( v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
      | ~ v3_pre_topc(X0,sK1)
      | ~ r2_hidden(sK4,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f285,f44])).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f285,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
      | ~ v3_pre_topc(X0,sK1)
      | ~ r2_hidden(sK4,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f284,f43])).

fof(f43,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f284,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
      | ~ v3_pre_topc(X0,sK1)
      | ~ r2_hidden(sK4,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f283,f42])).

fof(f42,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f283,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
      | ~ v3_pre_topc(X0,sK1)
      | ~ r2_hidden(sK4,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f282,f47])).

fof(f282,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
      | ~ v3_pre_topc(X0,sK1)
      | ~ r2_hidden(sK4,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f281,f46])).

fof(f281,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
      | ~ v3_pre_topc(X0,sK1)
      | ~ r2_hidden(sK4,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f280,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f280,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
      | ~ v3_pre_topc(X0,sK1)
      | ~ r2_hidden(sK4,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f279,f50])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f279,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
      | ~ v3_pre_topc(X0,sK1)
      | ~ r2_hidden(sK4,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f278,f49])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f278,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
      | ~ v3_pre_topc(X0,sK1)
      | ~ r2_hidden(sK4,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f277,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f277,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
      | ~ v3_pre_topc(X0,sK1)
      | ~ r2_hidden(sK4,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f276,f268])).

fof(f268,plain,(
    ~ r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f267,f70])).

fof(f267,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f266,f38])).

fof(f266,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f265,f41])).

fof(f265,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f264,f39])).

fof(f264,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f263,f44])).

fof(f263,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f262,f43])).

fof(f262,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f261,f42])).

fof(f261,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f260,f47])).

fof(f260,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f259,f46])).

fof(f259,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f258,f45])).

fof(f258,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f257,f50])).

fof(f257,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f256,f49])).

fof(f256,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f241,f48])).

fof(f241,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(duplicate_literal_removal,[],[f239])).

fof(f239,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(resolution,[],[f71,f65])).

fof(f65,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | X4 != X5
      | ~ r1_tmap_1(X1,X0,X2,X4)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).

fof(f71,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(forward_demodulation,[],[f35,f37])).

fof(f35,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f15])).

fof(f276,plain,(
    ! [X0] :
      ( r1_tmap_1(sK1,sK0,sK2,sK4)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
      | ~ v3_pre_topc(X0,sK1)
      | ~ r2_hidden(sK4,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK3)) ) ),
    inference(duplicate_literal_removal,[],[f273])).

fof(f273,plain,(
    ! [X0] :
      ( r1_tmap_1(sK1,sK0,sK2,sK4)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
      | ~ v3_pre_topc(X0,sK1)
      | ~ r2_hidden(sK4,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK3))
      | r1_tmap_1(sK1,sK0,sK2,sK4) ) ),
    inference(resolution,[],[f72,f67])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ v3_pre_topc(X4,X1)
      | ~ r2_hidden(X6,X4)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X6) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ v3_pre_topc(X4,X1)
      | ~ r2_hidden(X5,X4)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | X5 != X6
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X5) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ r2_hidden(X5,X4)
                              | ~ v3_pre_topc(X4,X1)
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ r2_hidden(X5,X4)
                              | ~ v3_pre_topc(X4,X1)
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( X5 = X6
                                  & r1_tarski(X4,u1_struct_0(X3))
                                  & r2_hidden(X5,X4)
                                  & v3_pre_topc(X4,X1) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tmap_1)).

fof(f72,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(forward_demodulation,[],[f34,f37])).

fof(f34,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:28:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (26949)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.41  % (26949)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f324,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(subsumption_resolution,[],[f323,f212])).
% 0.20/0.41  fof(f212,plain,(
% 0.20/0.41    ~v1_xboole_0(u1_struct_0(sK3))),
% 0.20/0.41    inference(subsumption_resolution,[],[f211,f178])).
% 0.20/0.41  fof(f178,plain,(
% 0.20/0.41    l1_pre_topc(sK3)),
% 0.20/0.41    inference(subsumption_resolution,[],[f165,f47])).
% 0.20/0.41  fof(f47,plain,(
% 0.20/0.41    l1_pre_topc(sK1)),
% 0.20/0.41    inference(cnf_transformation,[],[f15])).
% 0.20/0.41  fof(f15,plain,(
% 0.20/0.41    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.41    inference(flattening,[],[f14])).
% 0.20/0.41  fof(f14,plain,(
% 0.20/0.41    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.41    inference(ennf_transformation,[],[f13])).
% 0.20/0.41  fof(f13,negated_conjecture,(
% 0.20/0.41    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.20/0.41    inference(negated_conjecture,[],[f12])).
% 0.20/0.41  fof(f12,conjecture,(
% 0.20/0.41    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).
% 0.20/0.41  fof(f165,plain,(
% 0.20/0.41    ~l1_pre_topc(sK1) | l1_pre_topc(sK3)),
% 0.20/0.41    inference(resolution,[],[f41,f53])).
% 0.20/0.41  fof(f53,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f18])).
% 0.20/0.41  fof(f18,plain,(
% 0.20/0.41    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.41    inference(ennf_transformation,[],[f3])).
% 0.20/0.41  fof(f3,axiom,(
% 0.20/0.41    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.41  fof(f41,plain,(
% 0.20/0.41    m1_pre_topc(sK3,sK1)),
% 0.20/0.41    inference(cnf_transformation,[],[f15])).
% 0.20/0.41  fof(f211,plain,(
% 0.20/0.41    ~v1_xboole_0(u1_struct_0(sK3)) | ~l1_pre_topc(sK3)),
% 0.20/0.41    inference(resolution,[],[f73,f51])).
% 0.20/0.41  fof(f51,plain,(
% 0.20/0.41    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f16])).
% 0.20/0.41  fof(f16,plain,(
% 0.20/0.41    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.41    inference(ennf_transformation,[],[f2])).
% 0.20/0.41  fof(f2,axiom,(
% 0.20/0.41    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.41  fof(f73,plain,(
% 0.20/0.41    ~l1_struct_0(sK3) | ~v1_xboole_0(u1_struct_0(sK3))),
% 0.20/0.41    inference(resolution,[],[f39,f55])).
% 0.20/0.41  fof(f55,plain,(
% 0.20/0.41    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f21])).
% 0.20/0.41  fof(f21,plain,(
% 0.20/0.41    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.41    inference(flattening,[],[f20])).
% 0.20/0.41  fof(f20,plain,(
% 0.20/0.41    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.41    inference(ennf_transformation,[],[f4])).
% 0.20/0.41  fof(f4,axiom,(
% 0.20/0.41    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.41  fof(f39,plain,(
% 0.20/0.41    ~v2_struct_0(sK3)),
% 0.20/0.41    inference(cnf_transformation,[],[f15])).
% 0.20/0.41  fof(f323,plain,(
% 0.20/0.41    v1_xboole_0(u1_struct_0(sK3))),
% 0.20/0.41    inference(subsumption_resolution,[],[f322,f70])).
% 0.20/0.41  fof(f70,plain,(
% 0.20/0.41    m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.20/0.41    inference(forward_demodulation,[],[f36,f37])).
% 0.20/0.41  fof(f37,plain,(
% 0.20/0.41    sK4 = sK5),
% 0.20/0.41    inference(cnf_transformation,[],[f15])).
% 0.20/0.41  fof(f36,plain,(
% 0.20/0.41    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.20/0.41    inference(cnf_transformation,[],[f15])).
% 0.20/0.41  fof(f322,plain,(
% 0.20/0.41    ~m1_subset_1(sK4,u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3))),
% 0.20/0.41    inference(resolution,[],[f321,f64])).
% 0.20/0.41  fof(f64,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f33])).
% 0.20/0.41  fof(f33,plain,(
% 0.20/0.41    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.41    inference(flattening,[],[f32])).
% 0.20/0.41  fof(f32,plain,(
% 0.20/0.41    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.41    inference(ennf_transformation,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.41  fof(f321,plain,(
% 0.20/0.41    ~r2_hidden(sK4,u1_struct_0(sK3))),
% 0.20/0.41    inference(subsumption_resolution,[],[f319,f178])).
% 0.20/0.41  fof(f319,plain,(
% 0.20/0.41    ~r2_hidden(sK4,u1_struct_0(sK3)) | ~l1_pre_topc(sK3)),
% 0.20/0.41    inference(resolution,[],[f318,f52])).
% 0.20/0.42  fof(f52,plain,(
% 0.20/0.42    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,axiom,(
% 0.20/0.42    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.20/0.42  fof(f318,plain,(
% 0.20/0.42    ~m1_pre_topc(sK3,sK3) | ~r2_hidden(sK4,u1_struct_0(sK3))),
% 0.20/0.42    inference(subsumption_resolution,[],[f317,f41])).
% 0.20/0.42  fof(f317,plain,(
% 0.20/0.42    ~m1_pre_topc(sK3,sK1) | ~m1_pre_topc(sK3,sK3) | ~r2_hidden(sK4,u1_struct_0(sK3))),
% 0.20/0.42    inference(subsumption_resolution,[],[f315,f47])).
% 0.20/0.42  fof(f315,plain,(
% 0.20/0.42    ~l1_pre_topc(sK1) | ~m1_pre_topc(sK3,sK1) | ~m1_pre_topc(sK3,sK3) | ~r2_hidden(sK4,u1_struct_0(sK3))),
% 0.20/0.42    inference(resolution,[],[f314,f46])).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    v2_pre_topc(sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f314,plain,(
% 0.20/0.42    ( ! [X2] : (~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(sK3,X2) | ~m1_pre_topc(sK3,sK3) | ~r2_hidden(sK4,u1_struct_0(sK3))) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f313,f41])).
% 0.20/0.42  fof(f313,plain,(
% 0.20/0.42    ( ! [X2] : (~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(sK3,X2) | ~m1_pre_topc(sK3,sK3) | ~r2_hidden(sK4,u1_struct_0(sK3)) | ~m1_pre_topc(sK3,sK1)) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f312,f179])).
% 0.20/0.42  fof(f179,plain,(
% 0.20/0.42    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.42    inference(subsumption_resolution,[],[f166,f47])).
% 0.20/0.42  fof(f166,plain,(
% 0.20/0.42    ~l1_pre_topc(sK1) | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.42    inference(resolution,[],[f41,f54])).
% 0.20/0.42  fof(f54,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f19])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,axiom,(
% 0.20/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.42  fof(f312,plain,(
% 0.20/0.42    ( ! [X2] : (~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(sK3,X2) | ~m1_pre_topc(sK3,sK3) | ~r2_hidden(sK4,u1_struct_0(sK3)) | ~m1_pre_topc(sK3,sK1)) )),
% 0.20/0.42    inference(duplicate_literal_removal,[],[f311])).
% 0.20/0.42  fof(f311,plain,(
% 0.20/0.42    ( ! [X2] : (~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(sK3,X2) | ~m1_pre_topc(sK3,X2) | ~m1_pre_topc(sK3,sK3) | ~r2_hidden(sK4,u1_struct_0(sK3)) | ~m1_pre_topc(sK3,sK1)) )),
% 0.20/0.42    inference(resolution,[],[f309,f40])).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    v1_tsep_1(sK3,sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f309,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~v1_tsep_1(X0,sK1) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK3,X1) | ~m1_pre_topc(X0,sK3) | ~r2_hidden(sK4,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK1)) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f308,f47])).
% 0.20/0.42  fof(f308,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r2_hidden(sK4,u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK3,X1) | ~m1_pre_topc(X0,sK3) | ~l1_pre_topc(sK1) | ~v1_tsep_1(X0,sK1) | ~m1_pre_topc(X0,sK1)) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f307,f46])).
% 0.20/0.42  fof(f307,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r2_hidden(sK4,u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK3,X1) | ~m1_pre_topc(X0,sK3) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_tsep_1(X0,sK1) | ~m1_pre_topc(X0,sK1)) )),
% 0.20/0.42    inference(duplicate_literal_removal,[],[f306])).
% 0.20/0.42  fof(f306,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r2_hidden(sK4,u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK3,X1) | ~m1_pre_topc(X0,sK3) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~v1_tsep_1(X0,sK1) | ~m1_pre_topc(X0,sK1)) )),
% 0.20/0.42    inference(resolution,[],[f304,f69])).
% 0.20/0.42  fof(f69,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(u1_struct_0(X1),X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0)) )),
% 0.20/0.42    inference(equality_resolution,[],[f62])).
% 0.20/0.42  fof(f62,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v3_pre_topc(X2,X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f31])).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.42    inference(flattening,[],[f30])).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,axiom,(
% 0.20/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.20/0.42  fof(f304,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~v3_pre_topc(u1_struct_0(X0),sK1) | ~r2_hidden(sK4,u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK3,X1) | ~m1_pre_topc(X0,sK3)) )),
% 0.20/0.42    inference(resolution,[],[f290,f60])).
% 0.20/0.42  fof(f60,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f29])).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.42    inference(flattening,[],[f28])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,axiom,(
% 0.20/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.20/0.42  fof(f290,plain,(
% 0.20/0.42    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK3)) | ~v3_pre_topc(X0,sK1) | ~r2_hidden(sK4,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f289,f70])).
% 0.20/0.42  fof(f289,plain,(
% 0.20/0.42    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~v3_pre_topc(X0,sK1) | ~r2_hidden(sK4,X0) | ~r1_tarski(X0,u1_struct_0(sK3))) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f288,f38])).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f288,plain,(
% 0.20/0.42    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~v3_pre_topc(X0,sK1) | ~r2_hidden(sK4,X0) | ~r1_tarski(X0,u1_struct_0(sK3))) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f287,f41])).
% 0.20/0.42  fof(f287,plain,(
% 0.20/0.42    ( ! [X0] : (~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~v3_pre_topc(X0,sK1) | ~r2_hidden(sK4,X0) | ~r1_tarski(X0,u1_struct_0(sK3))) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f286,f39])).
% 0.20/0.42  fof(f286,plain,(
% 0.20/0.42    ( ! [X0] : (v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~v3_pre_topc(X0,sK1) | ~r2_hidden(sK4,X0) | ~r1_tarski(X0,u1_struct_0(sK3))) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f285,f44])).
% 0.20/0.42  fof(f44,plain,(
% 0.20/0.42    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f285,plain,(
% 0.20/0.42    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~v3_pre_topc(X0,sK1) | ~r2_hidden(sK4,X0) | ~r1_tarski(X0,u1_struct_0(sK3))) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f284,f43])).
% 0.20/0.42  fof(f43,plain,(
% 0.20/0.42    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f284,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~v3_pre_topc(X0,sK1) | ~r2_hidden(sK4,X0) | ~r1_tarski(X0,u1_struct_0(sK3))) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f283,f42])).
% 0.20/0.42  fof(f42,plain,(
% 0.20/0.42    v1_funct_1(sK2)),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f283,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~v3_pre_topc(X0,sK1) | ~r2_hidden(sK4,X0) | ~r1_tarski(X0,u1_struct_0(sK3))) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f282,f47])).
% 0.20/0.42  fof(f282,plain,(
% 0.20/0.42    ( ! [X0] : (~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~v3_pre_topc(X0,sK1) | ~r2_hidden(sK4,X0) | ~r1_tarski(X0,u1_struct_0(sK3))) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f281,f46])).
% 0.20/0.42  fof(f281,plain,(
% 0.20/0.42    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~v3_pre_topc(X0,sK1) | ~r2_hidden(sK4,X0) | ~r1_tarski(X0,u1_struct_0(sK3))) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f280,f45])).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    ~v2_struct_0(sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f280,plain,(
% 0.20/0.42    ( ! [X0] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~v3_pre_topc(X0,sK1) | ~r2_hidden(sK4,X0) | ~r1_tarski(X0,u1_struct_0(sK3))) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f279,f50])).
% 0.20/0.42  fof(f50,plain,(
% 0.20/0.42    l1_pre_topc(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f279,plain,(
% 0.20/0.42    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~v3_pre_topc(X0,sK1) | ~r2_hidden(sK4,X0) | ~r1_tarski(X0,u1_struct_0(sK3))) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f278,f49])).
% 0.20/0.42  fof(f49,plain,(
% 0.20/0.42    v2_pre_topc(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f278,plain,(
% 0.20/0.42    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~v3_pre_topc(X0,sK1) | ~r2_hidden(sK4,X0) | ~r1_tarski(X0,u1_struct_0(sK3))) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f277,f48])).
% 0.20/0.42  fof(f48,plain,(
% 0.20/0.42    ~v2_struct_0(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f277,plain,(
% 0.20/0.42    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~v3_pre_topc(X0,sK1) | ~r2_hidden(sK4,X0) | ~r1_tarski(X0,u1_struct_0(sK3))) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f276,f268])).
% 0.20/0.42  fof(f268,plain,(
% 0.20/0.42    ~r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.42    inference(subsumption_resolution,[],[f267,f70])).
% 0.20/0.42  fof(f267,plain,(
% 0.20/0.42    ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.20/0.42    inference(subsumption_resolution,[],[f266,f38])).
% 0.20/0.42  fof(f266,plain,(
% 0.20/0.42    ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.20/0.42    inference(subsumption_resolution,[],[f265,f41])).
% 0.20/0.42  fof(f265,plain,(
% 0.20/0.42    ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.20/0.42    inference(subsumption_resolution,[],[f264,f39])).
% 0.20/0.42  fof(f264,plain,(
% 0.20/0.42    ~r1_tmap_1(sK1,sK0,sK2,sK4) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.20/0.42    inference(subsumption_resolution,[],[f263,f44])).
% 0.20/0.42  fof(f263,plain,(
% 0.20/0.42    ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.20/0.42    inference(subsumption_resolution,[],[f262,f43])).
% 0.20/0.42  fof(f262,plain,(
% 0.20/0.42    ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.20/0.42    inference(subsumption_resolution,[],[f261,f42])).
% 0.20/0.42  fof(f261,plain,(
% 0.20/0.42    ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.20/0.42    inference(subsumption_resolution,[],[f260,f47])).
% 0.20/0.42  fof(f260,plain,(
% 0.20/0.42    ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.20/0.42    inference(subsumption_resolution,[],[f259,f46])).
% 0.20/0.42  fof(f259,plain,(
% 0.20/0.42    ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.20/0.42    inference(subsumption_resolution,[],[f258,f45])).
% 0.20/0.42  fof(f258,plain,(
% 0.20/0.42    ~r1_tmap_1(sK1,sK0,sK2,sK4) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.20/0.42    inference(subsumption_resolution,[],[f257,f50])).
% 0.20/0.42  fof(f257,plain,(
% 0.20/0.42    ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.20/0.42    inference(subsumption_resolution,[],[f256,f49])).
% 0.20/0.42  fof(f256,plain,(
% 0.20/0.42    ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.20/0.42    inference(subsumption_resolution,[],[f241,f48])).
% 0.20/0.42  fof(f241,plain,(
% 0.20/0.42    ~r1_tmap_1(sK1,sK0,sK2,sK4) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.20/0.42    inference(duplicate_literal_removal,[],[f239])).
% 0.20/0.42  fof(f239,plain,(
% 0.20/0.42    ~r1_tmap_1(sK1,sK0,sK2,sK4) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.42    inference(resolution,[],[f71,f65])).
% 0.20/0.42  fof(f65,plain,(
% 0.20/0.42    ( ! [X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X1,X0,X2,X5) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) )),
% 0.20/0.42    inference(equality_resolution,[],[f56])).
% 0.20/0.42  fof(f56,plain,(
% 0.20/0.42    ( ! [X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | X4 != X5 | ~r1_tmap_1(X1,X0,X2,X4) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f23])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.42    inference(flattening,[],[f22])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f10])).
% 0.20/0.42  fof(f10,axiom,(
% 0.20/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).
% 0.20/0.42  fof(f71,plain,(
% 0.20/0.42    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | ~r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.42    inference(forward_demodulation,[],[f35,f37])).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f276,plain,(
% 0.20/0.42    ( ! [X0] : (r1_tmap_1(sK1,sK0,sK2,sK4) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~v3_pre_topc(X0,sK1) | ~r2_hidden(sK4,X0) | ~r1_tarski(X0,u1_struct_0(sK3))) )),
% 0.20/0.42    inference(duplicate_literal_removal,[],[f273])).
% 0.20/0.42  fof(f273,plain,(
% 0.20/0.42    ( ! [X0] : (r1_tmap_1(sK1,sK0,sK2,sK4) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~v3_pre_topc(X0,sK1) | ~r2_hidden(sK4,X0) | ~r1_tarski(X0,u1_struct_0(sK3)) | r1_tmap_1(sK1,sK0,sK2,sK4)) )),
% 0.20/0.42    inference(resolution,[],[f72,f67])).
% 0.20/0.42  fof(f67,plain,(
% 0.20/0.42    ( ! [X6,X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~v3_pre_topc(X4,X1) | ~r2_hidden(X6,X4) | ~r1_tarski(X4,u1_struct_0(X3)) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6)) )),
% 0.20/0.42    inference(equality_resolution,[],[f57])).
% 0.20/0.42  fof(f57,plain,(
% 0.20/0.42    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~v3_pre_topc(X4,X1) | ~r2_hidden(X5,X4) | ~r1_tarski(X4,u1_struct_0(X3)) | X5 != X6 | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f25])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.42    inference(flattening,[],[f24])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,axiom,(
% 0.20/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tmap_1)).
% 0.20/0.42  fof(f72,plain,(
% 0.20/0.42    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.42    inference(forward_demodulation,[],[f34,f37])).
% 0.20/0.42  fof(f34,plain,(
% 0.20/0.42    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (26949)------------------------------
% 0.20/0.42  % (26949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (26949)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (26949)Memory used [KB]: 1791
% 0.20/0.42  % (26949)Time elapsed: 0.009 s
% 0.20/0.42  % (26949)------------------------------
% 0.20/0.42  % (26949)------------------------------
% 0.20/0.42  % (26935)Success in time 0.064 s
%------------------------------------------------------------------------------
