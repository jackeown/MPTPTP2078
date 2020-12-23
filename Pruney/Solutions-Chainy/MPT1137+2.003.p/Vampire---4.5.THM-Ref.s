%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 369 expanded)
%              Number of leaves         :    8 (  71 expanded)
%              Depth                    :   26
%              Number of atoms          :  254 (1982 expanded)
%              Number of equality atoms :   31 ( 232 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f301,plain,(
    $false ),
    inference(subsumption_resolution,[],[f300,f23])).

fof(f23,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_orders_2(X0,X2,X1)
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_orders_2(X0,X2,X1)
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ( r1_orders_2(X0,X2,X1)
                    & r1_orders_2(X0,X1,X2) )
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_orders_2)).

fof(f300,plain,(
    sK1 = sK2 ),
    inference(resolution,[],[f222,f184])).

fof(f184,plain,(
    v1_xboole_0(sK1) ),
    inference(resolution,[],[f180,f24])).

fof(f24,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f180,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f178,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f178,plain,(
    v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f177,f21])).

fof(f21,plain,(
    r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f177,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f176,f23])).

fof(f176,plain,
    ( sK1 = sK2
    | ~ r1_orders_2(sK0,sK1,sK2)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f175,f24])).

fof(f175,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = sK2
    | ~ r1_orders_2(sK0,sK1,sK2)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f161,f22])).

fof(f22,plain,(
    r1_orders_2(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f161,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK2 = X0
      | ~ r1_orders_2(sK0,X0,sK2)
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f160,f20])).

fof(f20,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | X0 = X1
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X1,X0)
      | ~ r1_orders_2(sK0,X0,X1)
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f159,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f159,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK0))
      | X0 = X1
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X1,X0)
      | ~ r1_orders_2(sK0,X0,X1)
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f152])).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK0))
      | X0 = X1
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X1,X0)
      | ~ r1_orders_2(sK0,X0,X1)
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f151,f41])).

fof(f151,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X2,u1_struct_0(sK0))
      | X2 = X3
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X3,X2)
      | ~ r1_orders_2(sK0,X2,X3) ) ),
    inference(subsumption_resolution,[],[f150,f25])).

fof(f25,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f150,plain,(
    ! [X2,X3] :
      ( X2 = X3
      | ~ r2_hidden(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X3,X2)
      | ~ r1_orders_2(sK0,X2,X3)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f149,f26])).

fof(f26,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f149,plain,(
    ! [X2,X3] :
      ( X2 = X3
      | ~ r2_hidden(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X3,X2)
      | ~ r1_orders_2(sK0,X2,X3)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f147,f35])).

fof(f35,plain,(
    ! [X0] :
      ( r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v5_orders_2(X0)
      <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v5_orders_2(X0)
      <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_orders_2)).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( ~ r4_relat_2(u1_orders_2(sK0),X1)
      | X0 = X2
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X2,X0)
      | ~ r1_orders_2(sK0,X0,X2) ) ),
    inference(resolution,[],[f144,f26])).

fof(f144,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ l1_orders_2(X9)
      | ~ r2_hidden(X8,X7)
      | X6 = X8
      | ~ r4_relat_2(u1_orders_2(X9),X7)
      | ~ r2_hidden(X6,X7)
      | ~ m1_subset_1(X6,u1_struct_0(X9))
      | ~ m1_subset_1(X8,u1_struct_0(X9))
      | ~ r1_orders_2(X9,X6,X8)
      | ~ r1_orders_2(X9,X8,X6) ) ),
    inference(duplicate_literal_removal,[],[f142])).

fof(f142,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ r2_hidden(X6,X7)
      | ~ r2_hidden(X8,X7)
      | X6 = X8
      | ~ r4_relat_2(u1_orders_2(X9),X7)
      | ~ l1_orders_2(X9)
      | ~ m1_subset_1(X6,u1_struct_0(X9))
      | ~ m1_subset_1(X8,u1_struct_0(X9))
      | ~ r1_orders_2(X9,X6,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X9))
      | ~ m1_subset_1(X6,u1_struct_0(X9))
      | ~ l1_orders_2(X9)
      | ~ r1_orders_2(X9,X8,X6) ) ),
    inference(resolution,[],[f90,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(f90,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ r2_hidden(k4_tarski(X8,X6),u1_orders_2(X9))
      | ~ r2_hidden(X6,X7)
      | ~ r2_hidden(X8,X7)
      | X6 = X8
      | ~ r4_relat_2(u1_orders_2(X9),X7)
      | ~ l1_orders_2(X9)
      | ~ m1_subset_1(X6,u1_struct_0(X9))
      | ~ m1_subset_1(X8,u1_struct_0(X9))
      | ~ r1_orders_2(X9,X6,X8) ) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ r2_hidden(X6,X7)
      | ~ r2_hidden(k4_tarski(X8,X6),u1_orders_2(X9))
      | ~ r2_hidden(X8,X7)
      | X6 = X8
      | ~ r4_relat_2(u1_orders_2(X9),X7)
      | ~ l1_orders_2(X9)
      | ~ m1_subset_1(X6,u1_struct_0(X9))
      | ~ m1_subset_1(X8,u1_struct_0(X9))
      | ~ l1_orders_2(X9)
      | ~ r1_orders_2(X9,X6,X8) ) ),
    inference(resolution,[],[f83,f37])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X0),u1_orders_2(X3))
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(k4_tarski(X0,X2),u1_orders_2(X3))
      | ~ r2_hidden(X0,X1)
      | X0 = X2
      | ~ r4_relat_2(u1_orders_2(X3),X1)
      | ~ l1_orders_2(X3) ) ),
    inference(resolution,[],[f27,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v1_relat_1(u1_orders_2(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f33,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f33,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X2,X3),X0)
      | ~ r2_hidden(k4_tarski(X3,X2),X0)
      | X2 = X3
      | ~ r4_relat_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( X2 = X3
              | ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( X2 = X3
              | ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X3,X2),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) )
             => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_2)).

fof(f222,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | sK2 = X0 ) ),
    inference(backward_demodulation,[],[f179,f191])).

fof(f191,plain,(
    sK2 = u1_struct_0(sK0) ),
    inference(resolution,[],[f183,f179])).

fof(f183,plain,(
    v1_xboole_0(sK2) ),
    inference(resolution,[],[f180,f20])).

fof(f179,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | u1_struct_0(sK0) = X0 ) ),
    inference(resolution,[],[f178,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:32:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.44  % (28900)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.45  % (28900)Refutation not found, incomplete strategy% (28900)------------------------------
% 0.22/0.45  % (28900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (28900)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.45  
% 0.22/0.45  % (28900)Memory used [KB]: 1663
% 0.22/0.45  % (28900)Time elapsed: 0.058 s
% 0.22/0.45  % (28900)------------------------------
% 0.22/0.45  % (28900)------------------------------
% 0.22/0.46  % (28893)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.46  % (28893)Refutation not found, incomplete strategy% (28893)------------------------------
% 0.22/0.46  % (28893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (28893)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.46  
% 0.22/0.46  % (28893)Memory used [KB]: 10618
% 0.22/0.46  % (28893)Time elapsed: 0.067 s
% 0.22/0.46  % (28893)------------------------------
% 0.22/0.46  % (28893)------------------------------
% 0.22/0.47  % (28912)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.50  % (28912)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f301,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(subsumption_resolution,[],[f300,f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    sK1 != sK2),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (X1 != X2 & r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0))),
% 0.22/0.50    inference(flattening,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : ((X1 != X2 & (r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2)) => X1 = X2))))),
% 0.22/0.50    inference(negated_conjecture,[],[f8])).
% 0.22/0.50  fof(f8,conjecture,(
% 0.22/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2)) => X1 = X2))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_orders_2)).
% 0.22/0.50  fof(f300,plain,(
% 0.22/0.50    sK1 = sK2),
% 0.22/0.50    inference(resolution,[],[f222,f184])).
% 0.22/0.50  fof(f184,plain,(
% 0.22/0.50    v1_xboole_0(sK1)),
% 0.22/0.50    inference(resolution,[],[f180,f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f180,plain,(
% 0.22/0.50    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | v1_xboole_0(X1)) )),
% 0.22/0.50    inference(resolution,[],[f178,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.50  fof(f178,plain,(
% 0.22/0.50    v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f177,f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    r1_orders_2(sK0,sK1,sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f177,plain,(
% 0.22/0.50    ~r1_orders_2(sK0,sK1,sK2) | v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f176,f23])).
% 0.22/0.50  fof(f176,plain,(
% 0.22/0.50    sK1 = sK2 | ~r1_orders_2(sK0,sK1,sK2) | v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f175,f24])).
% 0.22/0.50  fof(f175,plain,(
% 0.22/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = sK2 | ~r1_orders_2(sK0,sK1,sK2) | v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.50    inference(resolution,[],[f161,f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    r1_orders_2(sK0,sK2,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_orders_2(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK2 = X0 | ~r1_orders_2(sK0,X0,sK2) | v1_xboole_0(u1_struct_0(sK0))) )),
% 0.22/0.50    inference(resolution,[],[f160,f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f160,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | X0 = X1 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,X0) | ~r1_orders_2(sK0,X0,X1) | v1_xboole_0(u1_struct_0(sK0))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f159,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,u1_struct_0(sK0)) | X0 = X1 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,X0) | ~r1_orders_2(sK0,X0,X1) | v1_xboole_0(u1_struct_0(sK0))) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f152])).
% 0.22/0.50  fof(f152,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,u1_struct_0(sK0)) | X0 = X1 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,X0) | ~r1_orders_2(sK0,X0,X1) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 0.22/0.50    inference(resolution,[],[f151,f41])).
% 0.22/0.50  fof(f151,plain,(
% 0.22/0.50    ( ! [X2,X3] : (~r2_hidden(X3,u1_struct_0(sK0)) | ~r2_hidden(X2,u1_struct_0(sK0)) | X2 = X3 | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,X2) | ~r1_orders_2(sK0,X2,X3)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f150,f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    v5_orders_2(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f150,plain,(
% 0.22/0.50    ( ! [X2,X3] : (X2 = X3 | ~r2_hidden(X2,u1_struct_0(sK0)) | ~r2_hidden(X3,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,X2) | ~r1_orders_2(sK0,X2,X3) | ~v5_orders_2(sK0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f149,f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    l1_orders_2(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f149,plain,(
% 0.22/0.50    ( ! [X2,X3] : (X2 = X3 | ~r2_hidden(X2,u1_struct_0(sK0)) | ~r2_hidden(X3,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,X2) | ~r1_orders_2(sK0,X2,X3) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f147,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X0] : (r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : ((v5_orders_2(X0) <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : (l1_orders_2(X0) => (v5_orders_2(X0) <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_orders_2)).
% 0.22/0.50  fof(f147,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r4_relat_2(u1_orders_2(sK0),X1) | X0 = X2 | ~r2_hidden(X0,X1) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X0) | ~r1_orders_2(sK0,X0,X2)) )),
% 0.22/0.50    inference(resolution,[],[f144,f26])).
% 0.22/0.50  fof(f144,plain,(
% 0.22/0.50    ( ! [X6,X8,X7,X9] : (~l1_orders_2(X9) | ~r2_hidden(X8,X7) | X6 = X8 | ~r4_relat_2(u1_orders_2(X9),X7) | ~r2_hidden(X6,X7) | ~m1_subset_1(X6,u1_struct_0(X9)) | ~m1_subset_1(X8,u1_struct_0(X9)) | ~r1_orders_2(X9,X6,X8) | ~r1_orders_2(X9,X8,X6)) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f142])).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    ( ! [X6,X8,X7,X9] : (~r2_hidden(X6,X7) | ~r2_hidden(X8,X7) | X6 = X8 | ~r4_relat_2(u1_orders_2(X9),X7) | ~l1_orders_2(X9) | ~m1_subset_1(X6,u1_struct_0(X9)) | ~m1_subset_1(X8,u1_struct_0(X9)) | ~r1_orders_2(X9,X6,X8) | ~m1_subset_1(X8,u1_struct_0(X9)) | ~m1_subset_1(X6,u1_struct_0(X9)) | ~l1_orders_2(X9) | ~r1_orders_2(X9,X8,X6)) )),
% 0.22/0.50    inference(resolution,[],[f90,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r1_orders_2(X0,X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    ( ! [X6,X8,X7,X9] : (~r2_hidden(k4_tarski(X8,X6),u1_orders_2(X9)) | ~r2_hidden(X6,X7) | ~r2_hidden(X8,X7) | X6 = X8 | ~r4_relat_2(u1_orders_2(X9),X7) | ~l1_orders_2(X9) | ~m1_subset_1(X6,u1_struct_0(X9)) | ~m1_subset_1(X8,u1_struct_0(X9)) | ~r1_orders_2(X9,X6,X8)) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f88])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    ( ! [X6,X8,X7,X9] : (~r2_hidden(X6,X7) | ~r2_hidden(k4_tarski(X8,X6),u1_orders_2(X9)) | ~r2_hidden(X8,X7) | X6 = X8 | ~r4_relat_2(u1_orders_2(X9),X7) | ~l1_orders_2(X9) | ~m1_subset_1(X6,u1_struct_0(X9)) | ~m1_subset_1(X8,u1_struct_0(X9)) | ~l1_orders_2(X9) | ~r1_orders_2(X9,X6,X8)) )),
% 0.22/0.50    inference(resolution,[],[f83,f37])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X0),u1_orders_2(X3)) | ~r2_hidden(X2,X1) | ~r2_hidden(k4_tarski(X0,X2),u1_orders_2(X3)) | ~r2_hidden(X0,X1) | X0 = X2 | ~r4_relat_2(u1_orders_2(X3),X1) | ~l1_orders_2(X3)) )),
% 0.22/0.50    inference(resolution,[],[f27,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X0] : (v1_relat_1(u1_orders_2(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.50    inference(resolution,[],[f33,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(X2,X1) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X3,X2),X0) | X2 = X3 | ~r4_relat_2(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (r4_relat_2(X0,X1) <=> ! [X2,X3] : (X2 = X3 | ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1))) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (r4_relat_2(X0,X1) <=> ! [X2,X3] : (X2 = X3 | (~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)))) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r4_relat_2(X0,X1) <=> ! [X2,X3] : ((r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => X2 = X3)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_2)).
% 0.22/0.51  fof(f222,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_xboole_0(X0) | sK2 = X0) )),
% 0.22/0.51    inference(backward_demodulation,[],[f179,f191])).
% 0.22/0.51  fof(f191,plain,(
% 0.22/0.51    sK2 = u1_struct_0(sK0)),
% 0.22/0.51    inference(resolution,[],[f183,f179])).
% 0.22/0.51  fof(f183,plain,(
% 0.22/0.51    v1_xboole_0(sK2)),
% 0.22/0.51    inference(resolution,[],[f180,f20])).
% 0.22/0.51  fof(f179,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_xboole_0(X0) | u1_struct_0(sK0) = X0) )),
% 0.22/0.51    inference(resolution,[],[f178,f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (28912)------------------------------
% 0.22/0.51  % (28912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (28912)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (28912)Memory used [KB]: 1791
% 0.22/0.51  % (28912)Time elapsed: 0.106 s
% 0.22/0.51  % (28912)------------------------------
% 0.22/0.51  % (28912)------------------------------
% 0.22/0.51  % (28892)Success in time 0.141 s
%------------------------------------------------------------------------------
