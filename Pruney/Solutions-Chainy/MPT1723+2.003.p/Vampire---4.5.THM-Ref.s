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
% DateTime   : Thu Dec  3 13:18:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 455 expanded)
%              Number of leaves         :    4 (  76 expanded)
%              Depth                    :   36
%              Number of atoms          :  619 (4668 expanded)
%              Number of equality atoms :   22 (  45 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f359,plain,(
    $false ),
    inference(subsumption_resolution,[],[f358,f25])).

fof(f25,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                      & m1_pre_topc(X2,X3) )
                    | ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
                      & m1_pre_topc(X1,X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                      & m1_pre_topc(X2,X3) )
                    | ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
                      & m1_pre_topc(X1,X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
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
                   => ( ~ r1_tsep_1(X1,X2)
                     => ( ( m1_pre_topc(X2,X3)
                         => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) )
                        & ( m1_pre_topc(X1,X3)
                         => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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
                 => ( ~ r1_tsep_1(X1,X2)
                   => ( ( m1_pre_topc(X2,X3)
                       => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) )
                      & ( m1_pre_topc(X1,X3)
                       => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tmap_1)).

fof(f358,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f357,f20])).

fof(f20,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f357,plain,
    ( r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f356,f284])).

fof(f284,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f283,f16])).

fof(f16,plain,
    ( m1_pre_topc(sK2,sK3)
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f283,plain,
    ( ~ m1_pre_topc(sK1,sK3)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f282,f25])).

fof(f282,plain,
    ( ~ m1_pre_topc(sK1,sK3)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f281,f20])).

fof(f281,plain,
    ( ~ m1_pre_topc(sK1,sK3)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f280,f79])).

fof(f79,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(subsumption_resolution,[],[f78,f25])).

fof(f78,plain,
    ( v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK2) ),
    inference(subsumption_resolution,[],[f77,f22])).

fof(f22,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f77,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK2) ),
    inference(subsumption_resolution,[],[f76,f21])).

fof(f21,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f76,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK2) ),
    inference(subsumption_resolution,[],[f75,f27])).

fof(f27,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f75,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK2) ),
    inference(subsumption_resolution,[],[f74,f26])).

fof(f26,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f74,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK2) ),
    inference(duplicate_literal_removal,[],[f73])).

fof(f73,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK2) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X3] :
      ( k1_tsep_1(sK0,sK2,sK2) != k1_tsep_1(X2,X3,sK2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(sK2,X2)
      | v2_struct_0(X2)
      | m1_pre_topc(X3,sK2) ) ),
    inference(subsumption_resolution,[],[f57,f21])).

fof(f57,plain,(
    ! [X2,X3] :
      ( k1_tsep_1(sK0,sK2,sK2) != k1_tsep_1(X2,X3,sK2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X2)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,X2)
      | v2_struct_0(X2)
      | m1_pre_topc(X3,sK2) ) ),
    inference(superposition,[],[f29,f43])).

fof(f43,plain,(
    k1_tsep_1(sK0,sK2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(subsumption_resolution,[],[f42,f25])).

fof(f42,plain,
    ( v2_struct_0(sK0)
    | k1_tsep_1(sK0,sK2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(subsumption_resolution,[],[f41,f21])).

fof(f41,plain,
    ( v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | k1_tsep_1(sK0,sK2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(subsumption_resolution,[],[f40,f27])).

fof(f40,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | k1_tsep_1(sK0,sK2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(subsumption_resolution,[],[f33,f26])).

% (327)Refutation not found, incomplete strategy% (327)------------------------------
% (327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (327)Termination reason: Refutation not found, incomplete strategy

% (327)Memory used [KB]: 10618
% (327)Time elapsed: 0.097 s
% (327)------------------------------
% (327)------------------------------
fof(f33,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | k1_tsep_1(sK0,sK2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(resolution,[],[f28,f22])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k1_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0)
      | m1_pre_topc(X1,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
              <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
              <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
             => ( m1_pre_topc(X1,X2)
              <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tsep_1)).

fof(f280,plain,
    ( ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f279,f19])).

fof(f19,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f279,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f278,f18])).

fof(f18,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f278,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f277,f22])).

fof(f277,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f276,f21])).

fof(f276,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f275,f24])).

% (326)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
fof(f24,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f275,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f274,f23])).

fof(f23,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f274,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f273,f27])).

fof(f273,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f259,f26])).

fof(f259,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f254])).

fof(f254,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(resolution,[],[f31,f14])).

fof(f14,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2))
    | m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X0)
      | ~ m1_pre_topc(X1,X3)
      | ~ m1_pre_topc(X2,X4)
      | r1_tsep_1(X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                      | r1_tsep_1(X1,X2)
                      | ~ m1_pre_topc(X2,X4)
                      | ~ m1_pre_topc(X1,X3)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                      | r1_tsep_1(X1,X2)
                      | ~ m1_pre_topc(X2,X4)
                      | ~ m1_pre_topc(X1,X3)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X2,X4)
                          & m1_pre_topc(X1,X3) )
                       => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                          | r1_tsep_1(X1,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tmap_1)).

fof(f356,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f355,f90])).

fof(f90,plain,(
    m1_pre_topc(sK1,sK1) ),
    inference(subsumption_resolution,[],[f89,f25])).

fof(f89,plain,
    ( v2_struct_0(sK0)
    | m1_pre_topc(sK1,sK1) ),
    inference(subsumption_resolution,[],[f88,f24])).

fof(f88,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK1,sK1) ),
    inference(subsumption_resolution,[],[f87,f23])).

fof(f87,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK1,sK1) ),
    inference(subsumption_resolution,[],[f86,f27])).

fof(f86,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK1,sK1) ),
    inference(subsumption_resolution,[],[f85,f26])).

fof(f85,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK1,sK1) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK1,sK1) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X4,X5] :
      ( k1_tsep_1(sK0,sK1,sK1) != k1_tsep_1(X4,X5,sK1)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,X4)
      | ~ m1_pre_topc(sK1,X4)
      | v2_struct_0(X4)
      | m1_pre_topc(X5,sK1) ) ),
    inference(subsumption_resolution,[],[f58,f23])).

fof(f58,plain,(
    ! [X4,X5] :
      ( k1_tsep_1(sK0,sK1,sK1) != k1_tsep_1(X4,X5,sK1)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,X4)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X4)
      | v2_struct_0(X4)
      | m1_pre_topc(X5,sK1) ) ),
    inference(superposition,[],[f29,f47])).

fof(f47,plain,(
    k1_tsep_1(sK0,sK1,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(subsumption_resolution,[],[f46,f25])).

fof(f46,plain,
    ( v2_struct_0(sK0)
    | k1_tsep_1(sK0,sK1,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(subsumption_resolution,[],[f45,f23])).

fof(f45,plain,
    ( v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | k1_tsep_1(sK0,sK1,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(subsumption_resolution,[],[f44,f27])).

fof(f44,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | k1_tsep_1(sK0,sK1,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(subsumption_resolution,[],[f34,f26])).

fof(f34,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | k1_tsep_1(sK0,sK1,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(resolution,[],[f28,f24])).

fof(f355,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f354,f19])).

fof(f354,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f353,f18])).

fof(f353,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f352,f22])).

fof(f352,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f351,f21])).

fof(f351,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f350,f24])).

fof(f350,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f349,f23])).

fof(f349,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f348,f27])).

fof(f348,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f347,f26])).

fof(f347,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f346])).

fof(f346,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f272,f31])).

fof(f272,plain,(
    ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f271,f17])).

fof(f17,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f271,plain,
    ( ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f270,f25])).

fof(f270,plain,
    ( ~ m1_pre_topc(sK1,sK3)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f269,f20])).

fof(f269,plain,
    ( ~ m1_pre_topc(sK1,sK3)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f268,f79])).

fof(f268,plain,
    ( ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f267,f19])).

fof(f267,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f266,f18])).

fof(f266,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f265,f22])).

fof(f265,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f264,f21])).

fof(f264,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f263,f24])).

fof(f263,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f262,f23])).

fof(f262,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f261,f27])).

fof(f261,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f260,f26])).

fof(f260,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(duplicate_literal_removal,[],[f253])).

fof(f253,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(resolution,[],[f31,f15])).

fof(f15,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:04:33 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (317)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.49  % (324)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (323)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.50  % (324)Refutation not found, incomplete strategy% (324)------------------------------
% 0.21/0.50  % (324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (324)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (324)Memory used [KB]: 6140
% 0.21/0.50  % (324)Time elapsed: 0.078 s
% 0.21/0.50  % (324)------------------------------
% 0.21/0.50  % (324)------------------------------
% 0.21/0.50  % (325)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.50  % (319)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (318)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.50  % (330)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.50  % (336)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.51  % (337)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.51  % (321)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.51  % (330)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (325)Refutation not found, incomplete strategy% (325)------------------------------
% 0.21/0.51  % (325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (327)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.51  % (325)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (325)Memory used [KB]: 10618
% 0.21/0.51  % (325)Time elapsed: 0.070 s
% 0.21/0.51  % (325)------------------------------
% 0.21/0.51  % (325)------------------------------
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f359,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f358,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ~v2_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) & m1_pre_topc(X2,X3)) | (~m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f6])).
% 0.21/0.51  fof(f6,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) & m1_pre_topc(X2,X3)) | (~m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => ((m1_pre_topc(X2,X3) => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))) & (m1_pre_topc(X1,X3) => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)))))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f4])).
% 0.21/0.51  fof(f4,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => ((m1_pre_topc(X2,X3) => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))) & (m1_pre_topc(X1,X3) => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)))))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tmap_1)).
% 0.21/0.51  fof(f358,plain,(
% 0.21/0.51    v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f357,f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ~r1_tsep_1(sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f357,plain,(
% 0.21/0.51    r1_tsep_1(sK1,sK2) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f356,f284])).
% 0.21/0.51  fof(f284,plain,(
% 0.21/0.51    m1_pre_topc(sK2,sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f283,f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    m1_pre_topc(sK2,sK3) | m1_pre_topc(sK1,sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f283,plain,(
% 0.21/0.51    ~m1_pre_topc(sK1,sK3) | m1_pre_topc(sK2,sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f282,f25])).
% 0.21/0.51  fof(f282,plain,(
% 0.21/0.51    ~m1_pre_topc(sK1,sK3) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f281,f20])).
% 0.21/0.51  fof(f281,plain,(
% 0.21/0.51    ~m1_pre_topc(sK1,sK3) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f280,f79])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    m1_pre_topc(sK2,sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f78,f25])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    v2_struct_0(sK0) | m1_pre_topc(sK2,sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f77,f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    m1_pre_topc(sK2,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f76,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ~v2_struct_0(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f75,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f74,f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    v2_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK2)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK2)),
% 0.21/0.51    inference(equality_resolution,[],[f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X2,X3] : (k1_tsep_1(sK0,sK2,sK2) != k1_tsep_1(X2,X3,sK2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(sK2,X2) | v2_struct_0(X2) | m1_pre_topc(X3,sK2)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f57,f21])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X2,X3] : (k1_tsep_1(sK0,sK2,sK2) != k1_tsep_1(X2,X3,sK2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X2) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,X2) | v2_struct_0(X2) | m1_pre_topc(X3,sK2)) )),
% 0.21/0.51    inference(superposition,[],[f29,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    k1_tsep_1(sK0,sK2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.21/0.51    inference(subsumption_resolution,[],[f42,f25])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    v2_struct_0(sK0) | k1_tsep_1(sK0,sK2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.21/0.51    inference(subsumption_resolution,[],[f41,f21])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    v2_struct_0(sK2) | v2_struct_0(sK0) | k1_tsep_1(sK0,sK2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.21/0.51    inference(subsumption_resolution,[],[f40,f27])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | v2_struct_0(sK2) | v2_struct_0(sK0) | k1_tsep_1(sK0,sK2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.21/0.51    inference(subsumption_resolution,[],[f33,f26])).
% 0.21/0.51  % (327)Refutation not found, incomplete strategy% (327)------------------------------
% 0.21/0.51  % (327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (327)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (327)Memory used [KB]: 10618
% 0.21/0.51  % (327)Time elapsed: 0.097 s
% 0.21/0.51  % (327)------------------------------
% 0.21/0.51  % (327)------------------------------
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | v2_struct_0(sK0) | k1_tsep_1(sK0,sK2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.21/0.51    inference(resolution,[],[f28,f22])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0) | m1_pre_topc(X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tsep_1)).
% 0.21/0.51  fof(f280,plain,(
% 0.21/0.51    ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f279,f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    m1_pre_topc(sK3,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f279,plain,(
% 0.21/0.51    ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f278,f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ~v2_struct_0(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f278,plain,(
% 0.21/0.51    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f277,f22])).
% 0.21/0.51  fof(f277,plain,(
% 0.21/0.51    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f276,f21])).
% 0.21/0.51  fof(f276,plain,(
% 0.21/0.51    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f275,f24])).
% 0.21/0.51  % (326)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    m1_pre_topc(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f275,plain,(
% 0.21/0.51    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f274,f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ~v2_struct_0(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f274,plain,(
% 0.21/0.51    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f273,f27])).
% 0.21/0.51  fof(f273,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f259,f26])).
% 0.21/0.51  fof(f259,plain,(
% 0.21/0.51    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK3)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f254])).
% 0.21/0.51  fof(f254,plain,(
% 0.21/0.51    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK3)),
% 0.21/0.51    inference(resolution,[],[f31,f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2)) | m1_pre_topc(sK2,sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X4) | ~m1_pre_topc(X4,X0) | ~m1_pre_topc(X1,X3) | ~m1_pre_topc(X2,X4) | r1_tsep_1(X1,X2) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X4) | ~m1_pre_topc(X1,X3) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X4) | ~m1_pre_topc(X1,X3))) | (~m1_pre_topc(X4,X0) | v2_struct_0(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X2,X4) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) | r1_tsep_1(X1,X2))))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tmap_1)).
% 0.21/0.51  fof(f356,plain,(
% 0.21/0.51    ~m1_pre_topc(sK2,sK3) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f355,f90])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    m1_pre_topc(sK1,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f89,f25])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    v2_struct_0(sK0) | m1_pre_topc(sK1,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f88,f24])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | m1_pre_topc(sK1,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f87,f23])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | m1_pre_topc(sK1,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f86,f27])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | m1_pre_topc(sK1,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f85,f26])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | m1_pre_topc(sK1,sK1)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f84])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | m1_pre_topc(sK1,sK1)),
% 0.21/0.51    inference(equality_resolution,[],[f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X4,X5] : (k1_tsep_1(sK0,sK1,sK1) != k1_tsep_1(X4,X5,sK1) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(X5) | ~m1_pre_topc(X5,X4) | ~m1_pre_topc(sK1,X4) | v2_struct_0(X4) | m1_pre_topc(X5,sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f58,f23])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X4,X5] : (k1_tsep_1(sK0,sK1,sK1) != k1_tsep_1(X4,X5,sK1) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(X5) | ~m1_pre_topc(X5,X4) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X4) | v2_struct_0(X4) | m1_pre_topc(X5,sK1)) )),
% 0.21/0.51    inference(superposition,[],[f29,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    k1_tsep_1(sK0,sK1,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f46,f25])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    v2_struct_0(sK0) | k1_tsep_1(sK0,sK1,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f45,f23])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    v2_struct_0(sK1) | v2_struct_0(sK0) | k1_tsep_1(sK0,sK1,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f44,f27])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | k1_tsep_1(sK0,sK1,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f34,f26])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | k1_tsep_1(sK0,sK1,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.21/0.51    inference(resolution,[],[f28,f24])).
% 0.21/0.51  fof(f355,plain,(
% 0.21/0.51    ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(sK2,sK3) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f354,f19])).
% 0.21/0.51  fof(f354,plain,(
% 0.21/0.51    ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(sK2,sK3) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f353,f18])).
% 0.21/0.51  fof(f353,plain,(
% 0.21/0.51    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(sK2,sK3) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f352,f22])).
% 0.21/0.51  fof(f352,plain,(
% 0.21/0.51    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(sK2,sK3) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f351,f21])).
% 0.21/0.51  fof(f351,plain,(
% 0.21/0.51    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(sK2,sK3) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f350,f24])).
% 0.21/0.51  fof(f350,plain,(
% 0.21/0.51    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(sK2,sK3) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f349,f23])).
% 0.21/0.51  fof(f349,plain,(
% 0.21/0.51    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(sK2,sK3) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f348,f27])).
% 0.21/0.51  fof(f348,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(sK2,sK3) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f347,f26])).
% 0.21/0.51  fof(f347,plain,(
% 0.21/0.51    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(sK2,sK3) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f346])).
% 0.21/0.51  fof(f346,plain,(
% 0.21/0.51    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(sK2,sK3) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f272,f31])).
% 0.21/0.51  fof(f272,plain,(
% 0.21/0.51    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 0.21/0.51    inference(subsumption_resolution,[],[f271,f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) | m1_pre_topc(sK1,sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f271,plain,(
% 0.21/0.51    ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 0.21/0.51    inference(subsumption_resolution,[],[f270,f25])).
% 0.21/0.51  fof(f270,plain,(
% 0.21/0.51    ~m1_pre_topc(sK1,sK3) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 0.21/0.51    inference(subsumption_resolution,[],[f269,f20])).
% 0.21/0.51  fof(f269,plain,(
% 0.21/0.51    ~m1_pre_topc(sK1,sK3) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 0.21/0.51    inference(subsumption_resolution,[],[f268,f79])).
% 0.21/0.51  fof(f268,plain,(
% 0.21/0.51    ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 0.21/0.51    inference(subsumption_resolution,[],[f267,f19])).
% 0.21/0.51  fof(f267,plain,(
% 0.21/0.51    ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 0.21/0.51    inference(subsumption_resolution,[],[f266,f18])).
% 0.21/0.51  fof(f266,plain,(
% 0.21/0.51    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 0.21/0.51    inference(subsumption_resolution,[],[f265,f22])).
% 0.21/0.51  fof(f265,plain,(
% 0.21/0.51    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 0.21/0.51    inference(subsumption_resolution,[],[f264,f21])).
% 0.21/0.51  fof(f264,plain,(
% 0.21/0.51    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 0.21/0.51    inference(subsumption_resolution,[],[f263,f24])).
% 0.21/0.51  fof(f263,plain,(
% 0.21/0.51    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 0.21/0.51    inference(subsumption_resolution,[],[f262,f23])).
% 0.21/0.51  fof(f262,plain,(
% 0.21/0.51    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 0.21/0.51    inference(subsumption_resolution,[],[f261,f27])).
% 0.21/0.51  fof(f261,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 0.21/0.51    inference(subsumption_resolution,[],[f260,f26])).
% 0.21/0.51  fof(f260,plain,(
% 0.21/0.51    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f253])).
% 0.21/0.51  fof(f253,plain,(
% 0.21/0.51    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 0.21/0.51    inference(resolution,[],[f31,f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2)) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (330)------------------------------
% 0.21/0.51  % (330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (330)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (330)Memory used [KB]: 6268
% 0.21/0.51  % (330)Time elapsed: 0.075 s
% 0.21/0.51  % (330)------------------------------
% 0.21/0.51  % (330)------------------------------
% 0.21/0.51  % (316)Success in time 0.158 s
%------------------------------------------------------------------------------
