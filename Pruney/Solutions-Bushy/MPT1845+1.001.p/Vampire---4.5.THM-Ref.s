%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1845+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  162 (13181 expanded)
%              Number of leaves         :    4 (2459 expanded)
%              Depth                    :   53
%              Number of atoms          :  585 (48580 expanded)
%              Number of equality atoms :   26 (12628 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f241,plain,(
    $false ),
    inference(subsumption_resolution,[],[f240,f28])).

fof(f28,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_pre_topc(X1)
          & v2_pre_topc(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_pre_topc(X1)
          & v2_pre_topc(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v2_pre_topc(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v2_pre_topc(X1) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v2_pre_topc(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v2_pre_topc(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tex_2)).

fof(f240,plain,(
    ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f239,f30])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f239,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f238,f50])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f238,plain,(
    ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f237,f233])).

fof(f233,plain,
    ( m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(resolution,[],[f231,f163])).

fof(f163,plain,
    ( r1_tarski(sK2(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f162,f77])).

fof(f77,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f75,f30])).

fof(f75,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f74,f31])).

fof(f31,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f74,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | u1_struct_0(sK1) = X0 ) ),
    inference(superposition,[],[f56,f27])).

fof(f27,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f162,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r1_tarski(sK2(sK1),u1_pre_topc(sK0))
    | m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f161,f77])).

fof(f161,plain,
    ( r1_tarski(sK2(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f160,f29])).

fof(f29,plain,(
    ~ v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f160,plain,
    ( r1_tarski(sK2(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f132,f26])).

fof(f26,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f132,plain,
    ( r1_tarski(sK2(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK1)
    | m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_pre_topc(sK1) ),
    inference(superposition,[],[f47,f121])).

fof(f121,plain,(
    u1_pre_topc(sK0) = u1_pre_topc(sK1) ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X4,X5] :
      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X4,X5)
      | u1_pre_topc(sK1) = X5 ) ),
    inference(subsumption_resolution,[],[f112,f93])).

fof(f93,plain,(
    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f81,f26])).

fof(f81,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK1) ),
    inference(superposition,[],[f31,f77])).

fof(f112,plain,(
    ! [X4,X5] :
      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X4,X5)
      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | u1_pre_topc(sK1) = X5 ) ),
    inference(superposition,[],[f57,f80])).

fof(f80,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) ),
    inference(backward_demodulation,[],[f27,f77])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    ! [X0] :
      ( r1_tarski(sK2(X0),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f231,plain,(
    ~ r1_tarski(sK2(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f230,f28])).

fof(f230,plain,
    ( ~ r1_tarski(sK2(sK1),u1_pre_topc(sK0))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f229,f30])).

fof(f229,plain,
    ( ~ r1_tarski(sK2(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f228,f50])).

fof(f228,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r1_tarski(sK2(sK1),u1_pre_topc(sK0)) ),
    inference(resolution,[],[f227,f207])).

fof(f207,plain,
    ( ~ m1_subset_1(sK2(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(sK2(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f206,f28])).

fof(f206,plain,
    ( ~ m1_subset_1(sK2(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(sK2(sK1),u1_pre_topc(sK0))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f204,f30])).

fof(f204,plain,
    ( ~ m1_subset_1(sK2(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(sK2(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f203,f49])).

fof(f49,plain,(
    ! [X0,X3] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r1_tarski(X3,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f203,plain,(
    ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f202,f28])).

fof(f202,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f201,f30])).

fof(f201,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f200,f50])).

fof(f200,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f199,f180])).

fof(f180,plain,
    ( m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f179,f121])).

fof(f179,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1)) ),
    inference(forward_demodulation,[],[f105,f121])).

fof(f105,plain,
    ( m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1)) ),
    inference(subsumption_resolution,[],[f104,f29])).

fof(f104,plain,
    ( m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1))
    | v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f88,f26])).

fof(f88,plain,
    ( m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK1) ),
    inference(superposition,[],[f46,f77])).

fof(f46,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK2(X0)),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f199,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f198,f178])).

fof(f178,plain,
    ( m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f177,f121])).

fof(f177,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1)) ),
    inference(forward_demodulation,[],[f103,f121])).

fof(f103,plain,
    ( m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1)) ),
    inference(subsumption_resolution,[],[f102,f29])).

fof(f102,plain,
    ( m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1))
    | v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f86,f26])).

fof(f86,plain,
    ( m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK1) ),
    inference(superposition,[],[f41,f77])).

fof(f41,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK2(X0)),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f198,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f197,f159])).

fof(f159,plain,
    ( r2_hidden(sK4(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f158,f77])).

fof(f158,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r2_hidden(sK4(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK1),sK2(sK1)),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f157,f77])).

fof(f157,plain,
    ( r2_hidden(sK4(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK1),sK2(sK1)),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f156,f29])).

fof(f156,plain,
    ( r2_hidden(sK4(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK1),sK2(sK1)),u1_pre_topc(sK0))
    | v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f130,f26])).

fof(f130,plain,
    ( r2_hidden(sK4(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK1),sK2(sK1)),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK1) ),
    inference(superposition,[],[f43,f121])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK2(X0)),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f197,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK4(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f196,f155])).

fof(f155,plain,
    ( r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f154,f77])).

fof(f154,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK1),sK2(sK1)),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f153,f77])).

fof(f153,plain,
    ( r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK1),sK2(sK1)),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f152,f29])).

fof(f152,plain,
    ( r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK1),sK2(sK1)),u1_pre_topc(sK0))
    | v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f129,f26])).

fof(f129,plain,
    ( r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK1),sK2(sK1)),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK1) ),
    inference(superposition,[],[f42,f121])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK2(X0)),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f196,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(sK4(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f195,f28])).

fof(f195,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(sK4(sK1),u1_pre_topc(sK0))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f194,f30])).

fof(f194,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(sK4(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f191,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ r2_hidden(X2,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f191,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK3(sK1),sK4(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f190,f77])).

fof(f190,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK1),sK3(sK1),sK4(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f189,f121])).

fof(f189,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK1),sK3(sK1),sK4(sK1)),u1_pre_topc(sK1)) ),
    inference(forward_demodulation,[],[f188,f77])).

fof(f188,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK1),sK2(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK1),sK3(sK1),sK4(sK1)),u1_pre_topc(sK1)) ),
    inference(forward_demodulation,[],[f187,f121])).

fof(f187,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK1),sK2(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK1),sK3(sK1),sK4(sK1)),u1_pre_topc(sK1)) ),
    inference(forward_demodulation,[],[f186,f77])).

fof(f186,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK1),sK2(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK1),sK3(sK1),sK4(sK1)),u1_pre_topc(sK1)) ),
    inference(forward_demodulation,[],[f61,f121])).

fof(f61,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK1),sK2(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK1),sK3(sK1),sK4(sK1)),u1_pre_topc(sK1)) ),
    inference(subsumption_resolution,[],[f60,f26])).

fof(f60,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK1),sK2(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK1),sK3(sK1),sK4(sK1)),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f29,f44])).

fof(f44,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK2(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f227,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f225,f176])).

fof(f176,plain,
    ( m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK2(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f107,f121])).

fof(f107,plain,
    ( m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | m1_subset_1(sK2(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f106,f29])).

fof(f106,plain,
    ( m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | m1_subset_1(sK2(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f89,f26])).

fof(f89,plain,
    ( m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | m1_subset_1(sK2(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK1) ),
    inference(superposition,[],[f48,f77])).

fof(f48,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | m1_subset_1(sK2(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f225,plain,
    ( ~ m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK2(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f223,f175])).

fof(f175,plain,
    ( m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK2(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f95,f121])).

fof(f95,plain,
    ( m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | m1_subset_1(sK2(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f94,f29])).

fof(f94,plain,
    ( m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | m1_subset_1(sK2(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f82,f26])).

fof(f82,plain,
    ( m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | m1_subset_1(sK2(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK1) ),
    inference(superposition,[],[f33,f77])).

fof(f33,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | m1_subset_1(sK2(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f223,plain,
    ( ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f222,f28])).

fof(f222,plain,
    ( ~ m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f221,f30])).

fof(f221,plain,
    ( ~ m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f220,f50])).

fof(f220,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f219,f214])).

fof(f214,plain,
    ( r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f210,f144])).

fof(f144,plain,
    ( r1_tarski(sK2(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r2_hidden(sK3(sK1),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f143,f77])).

fof(f143,plain,
    ( r1_tarski(sK2(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | r2_hidden(sK3(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f142,f29])).

fof(f142,plain,
    ( r1_tarski(sK2(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f126,f26])).

fof(f126,plain,
    ( r1_tarski(sK2(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK1)
    | r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | v2_pre_topc(sK1) ),
    inference(superposition,[],[f38,f121])).

fof(f38,plain,(
    ! [X0] :
      ( r1_tarski(sK2(X0),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK3(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f210,plain,
    ( ~ r1_tarski(sK2(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r2_hidden(sK3(sK1),u1_pre_topc(sK0)) ),
    inference(resolution,[],[f207,f167])).

fof(f167,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r2_hidden(sK3(sK1),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f166,f121])).

fof(f166,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK2(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r2_hidden(sK3(sK1),u1_pre_topc(sK1)) ),
    inference(forward_demodulation,[],[f97,f121])).

fof(f97,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | r2_hidden(sK3(sK1),u1_pre_topc(sK1)) ),
    inference(subsumption_resolution,[],[f96,f29])).

fof(f96,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | r2_hidden(sK3(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f83,f26])).

fof(f83,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | r2_hidden(sK3(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1) ),
    inference(superposition,[],[f34,f77])).

fof(f34,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK3(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f219,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK3(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f218,f213])).

fof(f213,plain,
    ( r2_hidden(sK4(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f209,f147])).

fof(f147,plain,
    ( r1_tarski(sK2(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r2_hidden(sK4(sK1),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f146,f77])).

fof(f146,plain,
    ( r1_tarski(sK2(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | r2_hidden(sK4(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f145,f29])).

fof(f145,plain,
    ( r1_tarski(sK2(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | r2_hidden(sK4(sK1),u1_pre_topc(sK0))
    | v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f127,f26])).

fof(f127,plain,
    ( r1_tarski(sK2(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK1)
    | r2_hidden(sK4(sK1),u1_pre_topc(sK0))
    | v2_pre_topc(sK1) ),
    inference(superposition,[],[f39,f121])).

fof(f39,plain,(
    ! [X0] :
      ( r1_tarski(sK2(X0),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK4(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f209,plain,
    ( ~ r1_tarski(sK2(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r2_hidden(sK4(sK1),u1_pre_topc(sK0)) ),
    inference(resolution,[],[f207,f169])).

fof(f169,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r2_hidden(sK4(sK1),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f168,f121])).

fof(f168,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK2(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r2_hidden(sK4(sK1),u1_pre_topc(sK1)) ),
    inference(forward_demodulation,[],[f99,f121])).

fof(f99,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | r2_hidden(sK4(sK1),u1_pre_topc(sK1)) ),
    inference(subsumption_resolution,[],[f98,f29])).

fof(f98,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | r2_hidden(sK4(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f84,f26])).

fof(f84,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | r2_hidden(sK4(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1) ),
    inference(superposition,[],[f35,f77])).

fof(f35,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK4(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f218,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(sK4(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f217,f28])).

fof(f217,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(sK4(sK1),u1_pre_topc(sK0))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f216,f30])).

fof(f216,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(sK4(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f212,f45])).

fof(f212,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK3(sK1),sK4(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f208,f151])).

fof(f151,plain,
    ( r1_tarski(sK2(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK3(sK1),sK4(sK1)),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f150,f77])).

fof(f150,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r1_tarski(sK2(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK1),sK3(sK1),sK4(sK1)),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f149,f77])).

fof(f149,plain,
    ( r1_tarski(sK2(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK1),sK3(sK1),sK4(sK1)),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f148,f29])).

fof(f148,plain,
    ( r1_tarski(sK2(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK1),sK3(sK1),sK4(sK1)),u1_pre_topc(sK0))
    | v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f128,f26])).

fof(f128,plain,
    ( r1_tarski(sK2(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK1)
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK1),sK3(sK1),sK4(sK1)),u1_pre_topc(sK0))
    | v2_pre_topc(sK1) ),
    inference(superposition,[],[f40,f121])).

fof(f40,plain,(
    ! [X0] :
      ( r1_tarski(sK2(X0),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),u1_pre_topc(X0))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f208,plain,
    ( ~ r1_tarski(sK2(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK3(sK1),sK4(sK1)),u1_pre_topc(sK0)) ),
    inference(resolution,[],[f207,f193])).

fof(f193,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK3(sK1),sK4(sK1)),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f192,f121])).

fof(f192,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK2(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK3(sK1),sK4(sK1)),u1_pre_topc(sK1)) ),
    inference(forward_demodulation,[],[f101,f121])).

fof(f101,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK3(sK1),sK4(sK1)),u1_pre_topc(sK1)) ),
    inference(subsumption_resolution,[],[f100,f29])).

fof(f100,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK3(sK1),sK4(sK1)),u1_pre_topc(sK1))
    | v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f85,f26])).

fof(f85,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK3(sK1),sK4(sK1)),u1_pre_topc(sK1))
    | v2_pre_topc(sK1) ),
    inference(superposition,[],[f36,f77])).

fof(f36,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),u1_pre_topc(X0))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f237,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f234,f223])).

fof(f234,plain,
    ( m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(resolution,[],[f231,f141])).

fof(f141,plain,
    ( r1_tarski(sK2(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f140,f77])).

fof(f140,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r1_tarski(sK2(sK1),u1_pre_topc(sK0))
    | m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f139,f77])).

fof(f139,plain,
    ( r1_tarski(sK2(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f138,f29])).

fof(f138,plain,
    ( r1_tarski(sK2(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f125,f26])).

fof(f125,plain,
    ( r1_tarski(sK2(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK1)
    | m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_pre_topc(sK1) ),
    inference(superposition,[],[f37,f121])).

fof(f37,plain,(
    ! [X0] :
      ( r1_tarski(sK2(X0),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

%------------------------------------------------------------------------------
