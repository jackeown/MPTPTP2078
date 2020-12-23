%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1319+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:44 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 386 expanded)
%              Number of leaves         :    7 (  80 expanded)
%              Depth                    :   13
%              Number of atoms          :  165 (1714 expanded)
%              Number of equality atoms :   17 (  53 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f195,plain,(
    $false ),
    inference(global_subsumption,[],[f165,f194])).

fof(f194,plain,(
    sP5(sK7(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)),sK3,sK1,sK0) ),
    inference(forward_demodulation,[],[f193,f148])).

fof(f148,plain,(
    sK7(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)) = k3_xboole_0(sK1,sK6(sK0,sK1,sK2,sK7(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)))) ),
    inference(unit_resulting_resolution,[],[f143,f87])).

fof(f87,plain,(
    ! [X4,X5] :
      ( k3_xboole_0(sK1,sK6(sK0,sK1,X4,X5)) = X5
      | ~ sP5(X5,X4,sK1,sK0) ) ),
    inference(forward_demodulation,[],[f83,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f83,plain,(
    ! [X4,X5] :
      ( k3_xboole_0(sK6(sK0,sK1,X4,X5),sK1) = X5
      | ~ sP5(X5,X4,sK1,sK0) ) ),
    inference(superposition,[],[f27,f63])).

fof(f63,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1) ),
    inference(unit_resulting_resolution,[],[f22,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k1_tops_2(X0,X1,X2),k1_tops_2(X0,X1,X3))
                  & r1_tarski(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k1_tops_2(X0,X1,X2),k1_tops_2(X0,X1,X3))
                  & r1_tarski(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                   => ( r1_tarski(X2,X3)
                     => r1_tarski(k1_tops_2(X0,X1,X2),k1_tops_2(X0,X1,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                 => ( r1_tarski(X2,X3)
                   => r1_tarski(k1_tops_2(X0,X1,X2),k1_tops_2(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_tops_2)).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X2,X4),X1) = X4
      | ~ sP5(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tops_2(X0,X1,X2) = X3
                  <=> ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ? [X5] :
                              ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                              & r2_hidden(X5,X2)
                              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
                 => ( k1_tops_2(X0,X1,X2) = X3
                  <=> ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
                       => ( r2_hidden(X4,X3)
                        <=> ? [X5] :
                              ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                              & r2_hidden(X5,X2)
                              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_2)).

fof(f143,plain,(
    sP5(sK7(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)),sK2,sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f23,f22,f43,f127,f21,f122,f40])).

% (32696)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | sP5(X4,X2,X1,X0)
      | ~ r2_hidden(X4,k1_tops_2(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | sP5(X4,X2,X1,X0)
      | ~ r2_hidden(X4,X3)
      | k1_tops_2(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f122,plain,(
    m1_subset_1(k1_tops_2(sK0,sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))) ),
    inference(unit_resulting_resolution,[],[f23,f22,f21,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_2)).

fof(f21,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f10])).

fof(f127,plain,(
    m1_subset_1(sK7(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) ),
    inference(unit_resulting_resolution,[],[f43,f122,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f43,plain,(
    r2_hidden(sK7(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)),k1_tops_2(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f20,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f20,plain,(
    ~ r1_tarski(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f23,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f193,plain,(
    sP5(k3_xboole_0(sK1,sK6(sK0,sK1,sK2,sK7(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)))),sK3,sK1,sK0) ),
    inference(forward_demodulation,[],[f186,f33])).

fof(f186,plain,(
    sP5(k3_xboole_0(sK6(sK0,sK1,sK2,sK7(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),sK1),sK3,sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f161,f150,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( sP5(k3_xboole_0(X0,sK1),X1,sK1,sK0)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f42,f63])).

fof(f42,plain,(
    ! [X2,X0,X5,X1] :
      ( sP5(k9_subset_1(u1_struct_0(X0),X5,X1),X2,X1,X0)
      | ~ r2_hidden(X5,X2)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X5,X2)
      | k9_subset_1(u1_struct_0(X0),X5,X1) != X4
      | sP5(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f150,plain,(
    m1_subset_1(sK6(sK0,sK1,sK2,sK7(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f143,f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP5(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f161,plain,(
    r2_hidden(sK6(sK0,sK1,sK2,sK7(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),sK3) ),
    inference(unit_resulting_resolution,[],[f19,f151,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f151,plain,(
    r2_hidden(sK6(sK0,sK1,sK2,sK7(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3))),sK2) ),
    inference(unit_resulting_resolution,[],[f143,f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2,X4),X2)
      | ~ sP5(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f19,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f165,plain,(
    ~ sP5(sK7(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)),sK3,sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f23,f22,f44,f127,f18,f121,f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | ~ sP5(X4,X2,X1,X0)
      | r2_hidden(X4,k1_tops_2(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | ~ sP5(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k1_tops_2(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f121,plain,(
    m1_subset_1(k1_tops_2(sK0,sK1,sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))) ),
    inference(unit_resulting_resolution,[],[f23,f22,f18,f38])).

fof(f18,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f10])).

fof(f44,plain,(
    ~ r2_hidden(sK7(k1_tops_2(sK0,sK1,sK2),k1_tops_2(sK0,sK1,sK3)),k1_tops_2(sK0,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f20,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

%------------------------------------------------------------------------------
