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
% DateTime   : Thu Dec  3 13:11:14 EST 2020

% Result     : Theorem 2.40s
% Output     : Refutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 176 expanded)
%              Number of leaves         :   14 (  44 expanded)
%              Depth                    :   18
%              Number of atoms          :  184 ( 505 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1855,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1076,f1854])).

fof(f1854,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f1845])).

fof(f1845,plain,
    ( $false
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f54,f1101,f1834,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f1834,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK1,sK2),sK2)
    | ~ spl5_1 ),
    inference(superposition,[],[f1174,f96])).

fof(f96,plain,(
    sK2 = k2_xboole_0(k1_tops_1(sK0,sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f68,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f68,plain,(
    r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f41,f37,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tops_1)).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f1174,plain,
    ( ! [X0] : ~ r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k1_tops_1(sK0,sK2),X0))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f1163,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f1163,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f1089,f1141,f63])).

fof(f1141,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f192,f1090,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f1090,plain,
    ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f41,f53,f39,f974,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f974,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f973])).

fof(f973,plain,
    ( spl5_1
  <=> m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f192,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f87,f186])).

fof(f186,plain,(
    ! [X0] : k4_xboole_0(k1_tops_1(sK0,sK1),X0) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0) ),
    inference(unit_resulting_resolution,[],[f176,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f176,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f172,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f172,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f83,f143])).

fof(f143,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK1,X1)
      | r1_tarski(k1_tops_1(sK0,sK1),X1) ) ),
    inference(superposition,[],[f59,f108])).

fof(f108,plain,(
    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f81,f51])).

fof(f81,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f41,f39,f45])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f83,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f39,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f87,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f38,f82])).

fof(f82,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(unit_resulting_resolution,[],[f39,f46])).

fof(f38,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f22])).

fof(f1089,plain,
    ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f41,f974,f45])).

fof(f1101,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(u1_struct_0(sK0),sK2))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f54,f1092,f52])).

fof(f1092,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f974,f43])).

fof(f54,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f1076,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f1074])).

fof(f1074,plain,
    ( $false
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f53,f982,f990,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f990,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)),k4_xboole_0(sK1,sK2))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f980,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f980,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f975,f42])).

fof(f975,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f973])).

fof(f982,plain,
    ( ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)),sK1)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f980,f139])).

fof(f139,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4(X1,u1_struct_0(sK0)),sK1)
      | r1_tarski(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f91,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f91,plain,(
    ! [X0] :
      ( r2_hidden(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f83,f56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n009.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 16:18:11 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.44  % (18803)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.44  % (18795)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.46  % (18787)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.46  % (18784)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.49  % (18783)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.50  % (18809)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.50  % (18806)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.50  % (18786)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.52  % (18792)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.52  % (18785)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.52  % (18798)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.52  % (18788)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.53  % (18791)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.53  % (18782)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.53  % (18780)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.53  % (18789)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.53  % (18805)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.54  % (18781)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.54  % (18800)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.54  % (18796)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.54  % (18808)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.54  % (18794)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.55  % (18804)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.55  % (18802)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.55  % (18797)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.56  % (18797)Refutation not found, incomplete strategy% (18797)------------------------------
% 0.19/0.56  % (18797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.56  % (18797)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.56  
% 0.19/0.56  % (18797)Memory used [KB]: 10618
% 0.19/0.56  % (18797)Time elapsed: 0.167 s
% 0.19/0.56  % (18797)------------------------------
% 0.19/0.56  % (18797)------------------------------
% 0.19/0.56  % (18791)Refutation not found, incomplete strategy% (18791)------------------------------
% 0.19/0.56  % (18791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.56  % (18791)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.56  
% 0.19/0.56  % (18791)Memory used [KB]: 10746
% 0.19/0.56  % (18791)Time elapsed: 0.181 s
% 0.19/0.56  % (18791)------------------------------
% 0.19/0.56  % (18791)------------------------------
% 0.19/0.56  % (18801)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.56  % (18790)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.56  % (18790)Refutation not found, incomplete strategy% (18790)------------------------------
% 0.19/0.56  % (18790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.56  % (18790)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.56  
% 0.19/0.56  % (18790)Memory used [KB]: 10746
% 0.19/0.56  % (18790)Time elapsed: 0.168 s
% 0.19/0.56  % (18790)------------------------------
% 0.19/0.56  % (18790)------------------------------
% 0.19/0.56  % (18793)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.58  % (18802)Refutation not found, incomplete strategy% (18802)------------------------------
% 0.19/0.58  % (18802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.58  % (18802)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.58  
% 0.19/0.58  % (18802)Memory used [KB]: 10746
% 0.19/0.58  % (18802)Time elapsed: 0.189 s
% 0.19/0.58  % (18802)------------------------------
% 0.19/0.58  % (18802)------------------------------
% 0.19/0.58  % (18799)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.59  % (18807)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 2.15/0.62  % (18789)Refutation not found, incomplete strategy% (18789)------------------------------
% 2.15/0.62  % (18789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.62  % (18789)Termination reason: Refutation not found, incomplete strategy
% 2.15/0.62  
% 2.15/0.62  % (18789)Memory used [KB]: 11001
% 2.15/0.62  % (18789)Time elapsed: 0.227 s
% 2.15/0.62  % (18789)------------------------------
% 2.15/0.62  % (18789)------------------------------
% 2.40/0.66  % (18784)Refutation found. Thanks to Tanya!
% 2.40/0.66  % SZS status Theorem for theBenchmark
% 2.40/0.66  % SZS output start Proof for theBenchmark
% 2.40/0.66  fof(f1855,plain,(
% 2.40/0.66    $false),
% 2.40/0.66    inference(avatar_sat_refutation,[],[f1076,f1854])).
% 2.40/0.66  fof(f1854,plain,(
% 2.40/0.66    ~spl5_1),
% 2.40/0.66    inference(avatar_contradiction_clause,[],[f1845])).
% 2.40/0.66  fof(f1845,plain,(
% 2.40/0.66    $false | ~spl5_1),
% 2.40/0.66    inference(unit_resulting_resolution,[],[f54,f1101,f1834,f63])).
% 2.40/0.66  fof(f63,plain,(
% 2.40/0.66    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.40/0.66    inference(cnf_transformation,[],[f36])).
% 2.40/0.66  fof(f36,plain,(
% 2.40/0.66    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 2.40/0.66    inference(flattening,[],[f35])).
% 2.40/0.66  fof(f35,plain,(
% 2.40/0.66    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.40/0.66    inference(ennf_transformation,[],[f6])).
% 2.40/0.66  fof(f6,axiom,(
% 2.40/0.66    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 2.40/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 2.40/0.66  fof(f1834,plain,(
% 2.40/0.66    ~r1_xboole_0(k4_xboole_0(sK1,sK2),sK2) | ~spl5_1),
% 2.40/0.66    inference(superposition,[],[f1174,f96])).
% 2.40/0.66  fof(f96,plain,(
% 2.40/0.66    sK2 = k2_xboole_0(k1_tops_1(sK0,sK2),sK2)),
% 2.40/0.66    inference(unit_resulting_resolution,[],[f68,f51])).
% 2.40/0.66  fof(f51,plain,(
% 2.40/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.40/0.66    inference(cnf_transformation,[],[f27])).
% 2.40/0.66  fof(f27,plain,(
% 2.40/0.66    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.40/0.66    inference(ennf_transformation,[],[f4])).
% 2.40/0.66  fof(f4,axiom,(
% 2.40/0.66    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.40/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.40/0.66  fof(f68,plain,(
% 2.40/0.66    r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 2.40/0.66    inference(unit_resulting_resolution,[],[f41,f37,f45])).
% 2.40/0.66  fof(f45,plain,(
% 2.40/0.66    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 2.40/0.66    inference(cnf_transformation,[],[f25])).
% 2.40/0.66  fof(f25,plain,(
% 2.40/0.66    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.40/0.66    inference(ennf_transformation,[],[f17])).
% 2.40/0.66  fof(f17,axiom,(
% 2.40/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.40/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 2.40/0.66  fof(f37,plain,(
% 2.40/0.66    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.40/0.66    inference(cnf_transformation,[],[f22])).
% 2.40/0.66  fof(f22,plain,(
% 2.40/0.66    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.40/0.66    inference(flattening,[],[f21])).
% 2.40/0.66  fof(f21,plain,(
% 2.40/0.66    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.40/0.66    inference(ennf_transformation,[],[f20])).
% 2.40/0.66  fof(f20,negated_conjecture,(
% 2.40/0.66    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.40/0.66    inference(negated_conjecture,[],[f19])).
% 2.40/0.66  fof(f19,conjecture,(
% 2.40/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.40/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tops_1)).
% 2.40/0.66  fof(f41,plain,(
% 2.40/0.66    l1_pre_topc(sK0)),
% 2.40/0.66    inference(cnf_transformation,[],[f22])).
% 2.40/0.66  fof(f1174,plain,(
% 2.40/0.66    ( ! [X0] : (~r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k1_tops_1(sK0,sK2),X0))) ) | ~spl5_1),
% 2.40/0.66    inference(unit_resulting_resolution,[],[f1163,f60])).
% 2.40/0.66  fof(f60,plain,(
% 2.40/0.66    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.40/0.66    inference(cnf_transformation,[],[f34])).
% 2.40/0.66  fof(f34,plain,(
% 2.40/0.66    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.40/0.66    inference(ennf_transformation,[],[f7])).
% 2.40/0.66  fof(f7,axiom,(
% 2.40/0.66    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.40/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 2.40/0.66  fof(f1163,plain,(
% 2.40/0.66    ~r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2)) | ~spl5_1),
% 2.40/0.66    inference(unit_resulting_resolution,[],[f1089,f1141,f63])).
% 2.40/0.66  fof(f1141,plain,(
% 2.40/0.66    ~r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) | ~spl5_1),
% 2.40/0.66    inference(unit_resulting_resolution,[],[f192,f1090,f52])).
% 2.40/0.66  fof(f52,plain,(
% 2.40/0.66    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 2.40/0.66    inference(cnf_transformation,[],[f29])).
% 2.40/0.66  fof(f29,plain,(
% 2.40/0.66    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 2.40/0.66    inference(flattening,[],[f28])).
% 2.40/0.66  fof(f28,plain,(
% 2.40/0.66    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 2.40/0.66    inference(ennf_transformation,[],[f9])).
% 2.40/0.66  fof(f9,axiom,(
% 2.40/0.66    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.40/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 2.40/0.66  fof(f1090,plain,(
% 2.40/0.66    r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) | ~spl5_1),
% 2.40/0.66    inference(unit_resulting_resolution,[],[f41,f53,f39,f974,f44])).
% 2.40/0.66  fof(f44,plain,(
% 2.40/0.66    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))) )),
% 2.40/0.66    inference(cnf_transformation,[],[f24])).
% 2.40/0.66  fof(f24,plain,(
% 2.40/0.66    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.40/0.66    inference(flattening,[],[f23])).
% 2.40/0.66  fof(f23,plain,(
% 2.40/0.66    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.40/0.66    inference(ennf_transformation,[],[f18])).
% 2.40/0.66  fof(f18,axiom,(
% 2.40/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.40/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 2.40/0.66  fof(f974,plain,(
% 2.40/0.66    m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_1),
% 2.40/0.66    inference(avatar_component_clause,[],[f973])).
% 2.40/0.66  fof(f973,plain,(
% 2.40/0.66    spl5_1 <=> m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.40/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.40/0.66  fof(f39,plain,(
% 2.40/0.66    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.40/0.66    inference(cnf_transformation,[],[f22])).
% 2.40/0.66  fof(f53,plain,(
% 2.40/0.66    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.40/0.66    inference(cnf_transformation,[],[f5])).
% 2.40/0.66  fof(f5,axiom,(
% 2.40/0.66    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.40/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.40/0.66  fof(f192,plain,(
% 2.40/0.66    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 2.40/0.66    inference(backward_demodulation,[],[f87,f186])).
% 2.40/0.66  fof(f186,plain,(
% 2.40/0.66    ( ! [X0] : (k4_xboole_0(k1_tops_1(sK0,sK1),X0) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0)) )),
% 2.40/0.66    inference(unit_resulting_resolution,[],[f176,f46])).
% 2.40/0.66  fof(f46,plain,(
% 2.40/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)) )),
% 2.40/0.66    inference(cnf_transformation,[],[f26])).
% 2.40/0.66  fof(f26,plain,(
% 2.40/0.66    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.40/0.66    inference(ennf_transformation,[],[f13])).
% 2.40/0.66  fof(f13,axiom,(
% 2.40/0.66    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.40/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.40/0.66  fof(f176,plain,(
% 2.40/0.66    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.40/0.66    inference(unit_resulting_resolution,[],[f172,f42])).
% 2.40/0.66  fof(f42,plain,(
% 2.40/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.40/0.66    inference(cnf_transformation,[],[f15])).
% 2.40/0.66  fof(f15,axiom,(
% 2.40/0.66    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.40/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.40/0.66  fof(f172,plain,(
% 2.40/0.66    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 2.40/0.66    inference(unit_resulting_resolution,[],[f83,f143])).
% 2.40/0.66  fof(f143,plain,(
% 2.40/0.66    ( ! [X1] : (~r1_tarski(sK1,X1) | r1_tarski(k1_tops_1(sK0,sK1),X1)) )),
% 2.40/0.66    inference(superposition,[],[f59,f108])).
% 2.40/0.66  fof(f108,plain,(
% 2.40/0.66    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1)),
% 2.40/0.66    inference(unit_resulting_resolution,[],[f81,f51])).
% 2.40/0.66  fof(f81,plain,(
% 2.40/0.66    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 2.40/0.66    inference(unit_resulting_resolution,[],[f41,f39,f45])).
% 2.40/0.66  fof(f59,plain,(
% 2.40/0.66    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 2.40/0.66    inference(cnf_transformation,[],[f33])).
% 2.40/0.66  fof(f33,plain,(
% 2.40/0.66    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 2.40/0.66    inference(ennf_transformation,[],[f3])).
% 2.40/0.66  fof(f3,axiom,(
% 2.40/0.66    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 2.40/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 2.40/0.66  fof(f83,plain,(
% 2.40/0.66    r1_tarski(sK1,u1_struct_0(sK0))),
% 2.40/0.66    inference(unit_resulting_resolution,[],[f39,f43])).
% 2.40/0.66  fof(f43,plain,(
% 2.40/0.66    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.40/0.66    inference(cnf_transformation,[],[f15])).
% 2.40/0.66  fof(f87,plain,(
% 2.40/0.66    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 2.40/0.66    inference(backward_demodulation,[],[f38,f82])).
% 2.40/0.66  fof(f82,plain,(
% 2.40/0.66    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) )),
% 2.40/0.66    inference(unit_resulting_resolution,[],[f39,f46])).
% 2.40/0.66  fof(f38,plain,(
% 2.40/0.66    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 2.40/0.66    inference(cnf_transformation,[],[f22])).
% 2.40/0.66  fof(f1089,plain,(
% 2.40/0.66    r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2)) | ~spl5_1),
% 2.40/0.66    inference(unit_resulting_resolution,[],[f41,f974,f45])).
% 2.40/0.66  fof(f1101,plain,(
% 2.40/0.66    r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(u1_struct_0(sK0),sK2)) | ~spl5_1),
% 2.40/0.66    inference(unit_resulting_resolution,[],[f54,f1092,f52])).
% 2.40/0.66  fof(f1092,plain,(
% 2.40/0.66    r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) | ~spl5_1),
% 2.40/0.66    inference(unit_resulting_resolution,[],[f974,f43])).
% 2.40/0.66  fof(f54,plain,(
% 2.40/0.66    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.40/0.66    inference(cnf_transformation,[],[f8])).
% 2.40/0.66  fof(f8,axiom,(
% 2.40/0.66    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.40/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.40/0.66  fof(f1076,plain,(
% 2.40/0.66    spl5_1),
% 2.40/0.66    inference(avatar_contradiction_clause,[],[f1074])).
% 2.40/0.66  fof(f1074,plain,(
% 2.40/0.66    $false | spl5_1),
% 2.40/0.66    inference(unit_resulting_resolution,[],[f53,f982,f990,f56])).
% 2.40/0.66  fof(f56,plain,(
% 2.40/0.66    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.40/0.66    inference(cnf_transformation,[],[f32])).
% 2.40/0.66  fof(f32,plain,(
% 2.40/0.66    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.40/0.66    inference(ennf_transformation,[],[f1])).
% 2.40/0.66  fof(f1,axiom,(
% 2.40/0.66    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.40/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.40/0.66  fof(f990,plain,(
% 2.40/0.66    r2_hidden(sK4(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)),k4_xboole_0(sK1,sK2)) | spl5_1),
% 2.40/0.66    inference(unit_resulting_resolution,[],[f980,f57])).
% 2.40/0.66  fof(f57,plain,(
% 2.40/0.66    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.40/0.66    inference(cnf_transformation,[],[f32])).
% 2.40/0.66  fof(f980,plain,(
% 2.40/0.66    ~r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) | spl5_1),
% 2.40/0.66    inference(unit_resulting_resolution,[],[f975,f42])).
% 2.40/0.66  fof(f975,plain,(
% 2.40/0.66    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_1),
% 2.40/0.66    inference(avatar_component_clause,[],[f973])).
% 2.40/0.66  fof(f982,plain,(
% 2.40/0.66    ~r2_hidden(sK4(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)),sK1) | spl5_1),
% 2.40/0.66    inference(unit_resulting_resolution,[],[f980,f139])).
% 2.40/0.66  fof(f139,plain,(
% 2.40/0.66    ( ! [X1] : (~r2_hidden(sK4(X1,u1_struct_0(sK0)),sK1) | r1_tarski(X1,u1_struct_0(sK0))) )),
% 2.40/0.66    inference(resolution,[],[f91,f58])).
% 2.40/0.66  fof(f58,plain,(
% 2.40/0.66    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.40/0.66    inference(cnf_transformation,[],[f32])).
% 2.40/0.66  fof(f91,plain,(
% 2.40/0.66    ( ! [X0] : (r2_hidden(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1)) )),
% 2.40/0.66    inference(resolution,[],[f83,f56])).
% 2.40/0.66  % SZS output end Proof for theBenchmark
% 2.40/0.66  % (18784)------------------------------
% 2.40/0.66  % (18784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.40/0.66  % (18784)Termination reason: Refutation
% 2.40/0.66  
% 2.40/0.66  % (18784)Memory used [KB]: 7547
% 2.40/0.66  % (18784)Time elapsed: 0.286 s
% 2.40/0.66  % (18784)------------------------------
% 2.40/0.66  % (18784)------------------------------
% 2.40/0.67  % (18779)Success in time 0.327 s
%------------------------------------------------------------------------------
