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
% DateTime   : Thu Dec  3 13:12:26 EST 2020

% Result     : Theorem 7.19s
% Output     : Refutation 7.19s
% Verified   : 
% Statistics : Number of formulae       :  133 (1201 expanded)
%              Number of leaves         :   20 ( 429 expanded)
%              Depth                    :   17
%              Number of atoms          :  364 (7546 expanded)
%              Number of equality atoms :   79 ( 255 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2664,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2663,f1741])).

fof(f1741,plain,(
    k1_xboole_0 != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f296,f403,f353])).

fof(f353,plain,(
    ! [X6] :
      ( k1_xboole_0 != k1_tops_1(sK0,X6)
      | v2_tops_1(X6,sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(backward_demodulation,[],[f129,f341])).

fof(f341,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f117,f85])).

fof(f85,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f117,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f74,f87])).

fof(f87,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f74,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,
    ( ~ v2_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v4_pre_topc(sK2,sK0)
    & v2_tops_1(sK2,sK0)
    & v2_tops_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f66,f65,f64])).

fof(f64,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v4_pre_topc(X2,X0)
                & v2_tops_1(X2,X0)
                & v2_tops_1(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_1(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v4_pre_topc(X2,sK0)
              & v2_tops_1(X2,sK0)
              & v2_tops_1(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_tops_1(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & v4_pre_topc(X2,sK0)
            & v2_tops_1(X2,sK0)
            & v2_tops_1(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v2_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & v4_pre_topc(X2,sK0)
          & v2_tops_1(X2,sK0)
          & v2_tops_1(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( ? [X2] :
        ( ~ v2_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & v4_pre_topc(X2,sK0)
        & v2_tops_1(X2,sK0)
        & v2_tops_1(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & v4_pre_topc(sK2,sK0)
      & v2_tops_1(sK2,sK0)
      & v2_tops_1(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v4_pre_topc(X2,X0)
              & v2_tops_1(X2,X0)
              & v2_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v4_pre_topc(X2,X0)
              & v2_tops_1(X2,X0)
              & v2_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v4_pre_topc(X2,X0)
                    & v2_tops_1(X2,X0)
                    & v2_tops_1(X1,X0) )
                 => v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f30,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & v2_tops_1(X2,X0)
                  & v2_tops_1(X1,X0) )
               => v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_tops_1)).

fof(f129,plain,(
    ! [X6] :
      ( v2_tops_1(X6,sK0)
      | k1_xboole_0 != k1_tops_1(sK0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f74,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f403,plain,(
    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f299,f341])).

fof(f299,plain,(
    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f256,f262])).

fof(f262,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f75,f76,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f76,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f67])).

fof(f75,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f67])).

fof(f256,plain,(
    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f75,f76,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f296,plain,(
    ~ v2_tops_1(k2_xboole_0(sK1,sK2),sK0) ),
    inference(backward_demodulation,[],[f80,f262])).

fof(f80,plain,(
    ~ v2_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f2663,plain,(
    k1_xboole_0 = k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f2662,f1796])).

fof(f1796,plain,(
    k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f419,f1783])).

fof(f1783,plain,(
    k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK2)) ),
    inference(unit_resulting_resolution,[],[f417,f416,f348])).

fof(f348,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X1)
      | ~ v1_tops_1(X1,sK0) ) ),
    inference(backward_demodulation,[],[f124,f341])).

fof(f124,plain,(
    ! [X1] :
      ( k2_struct_0(sK0) = k2_pre_topc(sK0,X1)
      | ~ v1_tops_1(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f74,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f416,plain,(
    m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK2),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f323,f341])).

fof(f323,plain,(
    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f233,f234])).

fof(f234,plain,(
    k3_subset_1(u1_struct_0(sK0),sK2) = k4_xboole_0(u1_struct_0(sK0),sK2) ),
    inference(unit_resulting_resolution,[],[f76,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f233,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f76,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f417,plain,(
    v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK2),sK0) ),
    inference(backward_demodulation,[],[f324,f341])).

fof(f324,plain,(
    v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK2),sK0) ),
    inference(forward_demodulation,[],[f231,f234])).

fof(f231,plain,(
    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f74,f78,f76,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

fof(f78,plain,(
    v2_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f419,plain,(
    k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK2))) ),
    inference(backward_demodulation,[],[f328,f341])).

fof(f328,plain,(
    k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK2))) ),
    inference(forward_demodulation,[],[f327,f230])).

fof(f230,plain,(
    k1_xboole_0 = k1_tops_1(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f74,f78,f76,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f327,plain,(
    k1_tops_1(sK0,sK2) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK2))) ),
    inference(forward_demodulation,[],[f228,f234])).

fof(f228,plain,(
    k1_tops_1(sK0,sK2) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))) ),
    inference(unit_resulting_resolution,[],[f74,f76,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f2662,plain,(
    k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f2328,f2661])).

fof(f2661,plain,(
    k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f2660,f1783])).

fof(f2660,plain,(
    k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK2)) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f2659,f1382])).

fof(f1382,plain,(
    k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK1,sK2)) = k9_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),k4_xboole_0(k2_struct_0(sK0),sK2)) ),
    inference(forward_demodulation,[],[f1381,f1321])).

fof(f1321,plain,(
    ! [X0] : k7_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),X0) = k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK1,X0)) ),
    inference(forward_demodulation,[],[f1244,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1244,plain,(
    ! [X0] : k7_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),X0) = k4_xboole_0(k4_xboole_0(k2_struct_0(sK0),sK1),X0) ),
    inference(unit_resulting_resolution,[],[f378,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f378,plain,(
    m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f214,f341])).

fof(f214,plain,(
    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f143,f144])).

fof(f144,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f75,f101])).

fof(f143,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f75,f100])).

fof(f1381,plain,(
    k7_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),sK2) = k9_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),k4_xboole_0(k2_struct_0(sK0),sK2)) ),
    inference(forward_demodulation,[],[f1217,f387])).

fof(f387,plain,(
    k3_subset_1(k2_struct_0(sK0),sK2) = k4_xboole_0(k2_struct_0(sK0),sK2) ),
    inference(backward_demodulation,[],[f234,f341])).

fof(f1217,plain,(
    k7_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),sK2) = k9_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),k3_subset_1(k2_struct_0(sK0),sK2)) ),
    inference(unit_resulting_resolution,[],[f345,f378,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f345,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f76,f341])).

fof(f2659,plain,(
    k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK2)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),k4_xboole_0(k2_struct_0(sK0),sK2))) ),
    inference(forward_demodulation,[],[f2640,f1245])).

fof(f1245,plain,(
    ! [X0] : k9_subset_1(k2_struct_0(sK0),X0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k9_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),X0) ),
    inference(unit_resulting_resolution,[],[f378,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f2640,plain,(
    k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK2)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK2),k4_xboole_0(k2_struct_0(sK0),sK1))) ),
    inference(unit_resulting_resolution,[],[f418,f416,f379,f378,f426])).

fof(f426,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | ~ v1_tops_1(X1,sK0) ) ),
    inference(forward_demodulation,[],[f425,f341])).

fof(f425,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | ~ v1_tops_1(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f346,f341])).

fof(f346,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))
      | ~ v3_pre_topc(X0,sK0)
      | ~ v1_tops_1(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(backward_demodulation,[],[f116,f341])).

fof(f116,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))
      | ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_tops_1(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f115,f74])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))
      | ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_tops_1(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f73,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( v3_pre_topc(X2,X0)
                 => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).

fof(f73,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f379,plain,(
    v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    inference(backward_demodulation,[],[f215,f341])).

fof(f215,plain,(
    v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    inference(forward_demodulation,[],[f141,f144])).

fof(f141,plain,(
    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f74,f77,f75,f96])).

fof(f77,plain,(
    v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f418,plain,(
    v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK2),sK0) ),
    inference(backward_demodulation,[],[f326,f341])).

fof(f326,plain,(
    v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0) ),
    inference(forward_demodulation,[],[f229,f234])).

fof(f229,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f74,f79,f76,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f79,plain,(
    v4_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f2328,plain,(
    k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK1,sK2)))) ),
    inference(forward_demodulation,[],[f2295,f890])).

fof(f890,plain,(
    k3_subset_1(k2_struct_0(sK0),k2_xboole_0(sK1,sK2)) = k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f403,f101])).

fof(f2295,plain,(
    k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_xboole_0(sK1,sK2)))) ),
    inference(unit_resulting_resolution,[],[f403,f427])).

fof(f427,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) ) ),
    inference(forward_demodulation,[],[f347,f341])).

fof(f347,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) ) ),
    inference(backward_demodulation,[],[f123,f341])).

fof(f123,plain,(
    ! [X0] :
      ( k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f74,f89])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:38:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (4132)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (4147)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (4134)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (4136)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (4145)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (4135)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (4139)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (4152)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.30/0.52  % (4144)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.30/0.53  % (4154)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.30/0.53  % (4155)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.30/0.53  % (4158)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.30/0.53  % (4149)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.30/0.53  % (4149)Refutation not found, incomplete strategy% (4149)------------------------------
% 1.30/0.53  % (4149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (4149)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (4149)Memory used [KB]: 10618
% 1.30/0.53  % (4149)Time elapsed: 0.130 s
% 1.30/0.53  % (4149)------------------------------
% 1.30/0.53  % (4149)------------------------------
% 1.30/0.53  % (4146)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.30/0.53  % (4133)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.30/0.53  % (4157)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.30/0.53  % (4137)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.30/0.53  % (4156)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.45/0.54  % (4154)Refutation not found, incomplete strategy% (4154)------------------------------
% 1.45/0.54  % (4154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.54  % (4154)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.54  
% 1.45/0.54  % (4154)Memory used [KB]: 10874
% 1.45/0.54  % (4154)Time elapsed: 0.102 s
% 1.45/0.54  % (4154)------------------------------
% 1.45/0.54  % (4154)------------------------------
% 1.45/0.54  % (4138)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.45/0.54  % (4142)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.45/0.54  % (4150)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.45/0.54  % (4159)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.45/0.54  % (4141)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.45/0.55  % (4161)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.45/0.55  % (4140)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.45/0.55  % (4143)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.45/0.55  % (4160)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.45/0.55  % (4148)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.45/0.55  % (4151)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.45/0.55  % (4153)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 2.49/0.70  % (4163)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.49/0.71  % (4162)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.41/0.81  % (4137)Time limit reached!
% 3.41/0.81  % (4137)------------------------------
% 3.41/0.81  % (4137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.41/0.81  % (4137)Termination reason: Time limit
% 3.41/0.81  
% 3.41/0.81  % (4137)Memory used [KB]: 9722
% 3.41/0.81  % (4137)Time elapsed: 0.418 s
% 3.41/0.81  % (4137)------------------------------
% 3.41/0.81  % (4137)------------------------------
% 3.63/0.90  % (4133)Time limit reached!
% 3.63/0.90  % (4133)------------------------------
% 3.63/0.90  % (4133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.63/0.90  % (4133)Termination reason: Time limit
% 3.63/0.90  % (4133)Termination phase: Saturation
% 3.63/0.90  
% 3.63/0.90  % (4133)Memory used [KB]: 7803
% 3.63/0.90  % (4133)Time elapsed: 0.500 s
% 3.63/0.90  % (4133)------------------------------
% 3.63/0.90  % (4133)------------------------------
% 3.63/0.91  % (4144)Time limit reached!
% 3.63/0.91  % (4144)------------------------------
% 3.63/0.91  % (4144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.63/0.91  % (4144)Termination reason: Time limit
% 3.63/0.91  
% 3.63/0.91  % (4144)Memory used [KB]: 10106
% 3.63/0.91  % (4144)Time elapsed: 0.508 s
% 3.63/0.91  % (4144)------------------------------
% 3.63/0.91  % (4144)------------------------------
% 3.63/0.92  % (4164)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.63/0.92  % (4142)Time limit reached!
% 3.63/0.92  % (4142)------------------------------
% 3.63/0.92  % (4142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.63/0.92  % (4142)Termination reason: Time limit
% 3.63/0.92  
% 3.63/0.92  % (4142)Memory used [KB]: 17142
% 3.63/0.92  % (4142)Time elapsed: 0.527 s
% 3.63/0.92  % (4142)------------------------------
% 3.63/0.92  % (4142)------------------------------
% 4.24/0.93  % (4132)Time limit reached!
% 4.24/0.93  % (4132)------------------------------
% 4.24/0.93  % (4132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.24/0.93  % (4132)Termination reason: Time limit
% 4.24/0.93  
% 4.24/0.93  % (4132)Memory used [KB]: 5373
% 4.24/0.93  % (4132)Time elapsed: 0.523 s
% 4.24/0.93  % (4132)------------------------------
% 4.24/0.93  % (4132)------------------------------
% 4.63/1.00  % (4165)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.63/1.01  % (4148)Time limit reached!
% 4.63/1.01  % (4148)------------------------------
% 4.63/1.01  % (4148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.63/1.01  % (4148)Termination reason: Time limit
% 4.63/1.01  
% 4.63/1.01  % (4148)Memory used [KB]: 17270
% 4.63/1.01  % (4148)Time elapsed: 0.608 s
% 4.63/1.01  % (4148)------------------------------
% 4.63/1.01  % (4148)------------------------------
% 4.63/1.02  % (4160)Time limit reached!
% 4.63/1.02  % (4160)------------------------------
% 4.63/1.02  % (4160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.63/1.03  % (4167)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.63/1.03  % (4139)Time limit reached!
% 4.63/1.03  % (4139)------------------------------
% 4.63/1.03  % (4139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.63/1.03  % (4139)Termination reason: Time limit
% 4.63/1.03  
% 4.63/1.03  % (4139)Memory used [KB]: 12537
% 4.63/1.03  % (4139)Time elapsed: 0.624 s
% 4.63/1.03  % (4139)------------------------------
% 4.63/1.03  % (4139)------------------------------
% 4.63/1.04  % (4166)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.63/1.04  % (4160)Termination reason: Time limit
% 4.63/1.04  
% 4.63/1.04  % (4160)Memory used [KB]: 7419
% 4.63/1.04  % (4160)Time elapsed: 0.621 s
% 4.63/1.04  % (4160)------------------------------
% 4.63/1.04  % (4160)------------------------------
% 5.06/1.07  % (4168)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.97/1.13  % (4169)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.20/1.18  % (4170)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.20/1.21  % (4171)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.20/1.21  % (4153)Time limit reached!
% 6.20/1.21  % (4153)------------------------------
% 6.20/1.21  % (4153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.20/1.21  % (4153)Termination reason: Time limit
% 6.20/1.21  % (4153)Termination phase: Saturation
% 6.20/1.21  
% 6.20/1.21  % (4153)Memory used [KB]: 7419
% 6.20/1.21  % (4153)Time elapsed: 0.800 s
% 6.20/1.21  % (4153)------------------------------
% 6.20/1.21  % (4153)------------------------------
% 7.19/1.28  % (4170)Refutation found. Thanks to Tanya!
% 7.19/1.28  % SZS status Theorem for theBenchmark
% 7.19/1.28  % SZS output start Proof for theBenchmark
% 7.19/1.28  fof(f2664,plain,(
% 7.19/1.28    $false),
% 7.19/1.28    inference(subsumption_resolution,[],[f2663,f1741])).
% 7.19/1.28  fof(f1741,plain,(
% 7.19/1.28    k1_xboole_0 != k1_tops_1(sK0,k2_xboole_0(sK1,sK2))),
% 7.19/1.28    inference(unit_resulting_resolution,[],[f296,f403,f353])).
% 7.19/1.28  fof(f353,plain,(
% 7.19/1.28    ( ! [X6] : (k1_xboole_0 != k1_tops_1(sK0,X6) | v2_tops_1(X6,sK0) | ~m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 7.19/1.28    inference(backward_demodulation,[],[f129,f341])).
% 7.19/1.28  fof(f341,plain,(
% 7.19/1.28    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 7.19/1.28    inference(unit_resulting_resolution,[],[f117,f85])).
% 7.19/1.28  fof(f85,plain,(
% 7.19/1.28    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 7.19/1.28    inference(cnf_transformation,[],[f34])).
% 7.19/1.28  fof(f34,plain,(
% 7.19/1.28    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 7.19/1.28    inference(ennf_transformation,[],[f19])).
% 7.19/1.28  fof(f19,axiom,(
% 7.19/1.28    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 7.19/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 7.19/1.28  fof(f117,plain,(
% 7.19/1.28    l1_struct_0(sK0)),
% 7.19/1.28    inference(unit_resulting_resolution,[],[f74,f87])).
% 7.19/1.28  fof(f87,plain,(
% 7.19/1.28    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.19/1.28    inference(cnf_transformation,[],[f36])).
% 7.19/1.28  fof(f36,plain,(
% 7.19/1.28    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.19/1.28    inference(ennf_transformation,[],[f20])).
% 7.19/1.28  fof(f20,axiom,(
% 7.19/1.28    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.19/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 7.19/1.28  fof(f74,plain,(
% 7.19/1.28    l1_pre_topc(sK0)),
% 7.19/1.28    inference(cnf_transformation,[],[f67])).
% 7.19/1.28  fof(f67,plain,(
% 7.19/1.28    ((~v2_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v4_pre_topc(sK2,sK0) & v2_tops_1(sK2,sK0) & v2_tops_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 7.19/1.28    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f66,f65,f64])).
% 7.19/1.28  fof(f64,plain,(
% 7.19/1.28    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) & v4_pre_topc(X2,X0) & v2_tops_1(X2,X0) & v2_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tops_1(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v4_pre_topc(X2,sK0) & v2_tops_1(X2,sK0) & v2_tops_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 7.19/1.28    introduced(choice_axiom,[])).
% 7.19/1.28  fof(f65,plain,(
% 7.19/1.28    ? [X1] : (? [X2] : (~v2_tops_1(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v4_pre_topc(X2,sK0) & v2_tops_1(X2,sK0) & v2_tops_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v2_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v4_pre_topc(X2,sK0) & v2_tops_1(X2,sK0) & v2_tops_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 7.19/1.28    introduced(choice_axiom,[])).
% 7.19/1.28  fof(f66,plain,(
% 7.19/1.28    ? [X2] : (~v2_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v4_pre_topc(X2,sK0) & v2_tops_1(X2,sK0) & v2_tops_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v4_pre_topc(sK2,sK0) & v2_tops_1(sK2,sK0) & v2_tops_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 7.19/1.28    introduced(choice_axiom,[])).
% 7.19/1.28  fof(f33,plain,(
% 7.19/1.28    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) & v4_pre_topc(X2,X0) & v2_tops_1(X2,X0) & v2_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.19/1.28    inference(flattening,[],[f32])).
% 7.19/1.28  fof(f32,plain,(
% 7.19/1.28    ? [X0] : (? [X1] : (? [X2] : ((~v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) & (v4_pre_topc(X2,X0) & v2_tops_1(X2,X0) & v2_tops_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.19/1.28    inference(ennf_transformation,[],[f31])).
% 7.19/1.28  fof(f31,negated_conjecture,(
% 7.19/1.28    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v2_tops_1(X2,X0) & v2_tops_1(X1,X0)) => v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 7.19/1.28    inference(negated_conjecture,[],[f30])).
% 7.19/1.28  fof(f30,conjecture,(
% 7.19/1.28    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v2_tops_1(X2,X0) & v2_tops_1(X1,X0)) => v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 7.19/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_tops_1)).
% 7.19/1.28  fof(f129,plain,(
% 7.19/1.28    ( ! [X6] : (v2_tops_1(X6,sK0) | k1_xboole_0 != k1_tops_1(sK0,X6) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 7.19/1.28    inference(resolution,[],[f74,f95])).
% 7.19/1.28  fof(f95,plain,(
% 7.19/1.28    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.19/1.28    inference(cnf_transformation,[],[f70])).
% 7.19/1.28  fof(f70,plain,(
% 7.19/1.28    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.19/1.28    inference(nnf_transformation,[],[f41])).
% 7.19/1.28  fof(f41,plain,(
% 7.19/1.28    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.19/1.28    inference(ennf_transformation,[],[f29])).
% 7.19/1.28  fof(f29,axiom,(
% 7.19/1.28    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 7.19/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 7.19/1.28  fof(f403,plain,(
% 7.19/1.28    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k2_struct_0(sK0)))),
% 7.19/1.28    inference(backward_demodulation,[],[f299,f341])).
% 7.19/1.28  fof(f299,plain,(
% 7.19/1.28    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.19/1.28    inference(forward_demodulation,[],[f256,f262])).
% 7.19/1.28  fof(f262,plain,(
% 7.19/1.28    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)),
% 7.19/1.28    inference(unit_resulting_resolution,[],[f75,f76,f113])).
% 7.19/1.28  fof(f113,plain,(
% 7.19/1.28    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.19/1.28    inference(cnf_transformation,[],[f61])).
% 7.19/1.28  fof(f61,plain,(
% 7.19/1.28    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.19/1.28    inference(flattening,[],[f60])).
% 7.19/1.28  fof(f60,plain,(
% 7.19/1.28    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.19/1.28    inference(ennf_transformation,[],[f12])).
% 7.19/1.28  fof(f12,axiom,(
% 7.19/1.28    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 7.19/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 7.19/1.28  fof(f76,plain,(
% 7.19/1.28    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.19/1.28    inference(cnf_transformation,[],[f67])).
% 7.19/1.28  fof(f75,plain,(
% 7.19/1.28    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.19/1.28    inference(cnf_transformation,[],[f67])).
% 7.19/1.28  fof(f256,plain,(
% 7.19/1.28    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.19/1.28    inference(unit_resulting_resolution,[],[f75,f76,f112])).
% 7.19/1.28  fof(f112,plain,(
% 7.19/1.28    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.19/1.28    inference(cnf_transformation,[],[f59])).
% 7.19/1.28  fof(f59,plain,(
% 7.19/1.28    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.19/1.28    inference(flattening,[],[f58])).
% 7.19/1.28  fof(f58,plain,(
% 7.19/1.28    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.19/1.28    inference(ennf_transformation,[],[f10])).
% 7.19/1.28  fof(f10,axiom,(
% 7.19/1.28    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 7.19/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 7.19/1.28  fof(f296,plain,(
% 7.19/1.28    ~v2_tops_1(k2_xboole_0(sK1,sK2),sK0)),
% 7.19/1.28    inference(backward_demodulation,[],[f80,f262])).
% 7.19/1.28  fof(f80,plain,(
% 7.19/1.28    ~v2_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 7.19/1.28    inference(cnf_transformation,[],[f67])).
% 7.19/1.28  fof(f2663,plain,(
% 7.19/1.28    k1_xboole_0 = k1_tops_1(sK0,k2_xboole_0(sK1,sK2))),
% 7.19/1.28    inference(forward_demodulation,[],[f2662,f1796])).
% 7.19/1.28  fof(f1796,plain,(
% 7.19/1.28    k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))),
% 7.19/1.28    inference(backward_demodulation,[],[f419,f1783])).
% 7.19/1.28  fof(f1783,plain,(
% 7.19/1.28    k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK2))),
% 7.19/1.28    inference(unit_resulting_resolution,[],[f417,f416,f348])).
% 7.19/1.28  fof(f348,plain,(
% 7.19/1.28    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X1) | ~v1_tops_1(X1,sK0)) )),
% 7.19/1.28    inference(backward_demodulation,[],[f124,f341])).
% 7.19/1.28  fof(f124,plain,(
% 7.19/1.28    ( ! [X1] : (k2_struct_0(sK0) = k2_pre_topc(sK0,X1) | ~v1_tops_1(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 7.19/1.28    inference(resolution,[],[f74,f90])).
% 7.19/1.28  fof(f90,plain,(
% 7.19/1.28    ( ! [X0,X1] : (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.19/1.28    inference(cnf_transformation,[],[f68])).
% 7.19/1.28  fof(f68,plain,(
% 7.19/1.28    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.19/1.28    inference(nnf_transformation,[],[f39])).
% 7.19/1.28  fof(f39,plain,(
% 7.19/1.28    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.19/1.28    inference(ennf_transformation,[],[f23])).
% 7.19/1.28  fof(f23,axiom,(
% 7.19/1.28    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 7.19/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 7.19/1.28  fof(f416,plain,(
% 7.19/1.28    m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK2),k1_zfmisc_1(k2_struct_0(sK0)))),
% 7.19/1.28    inference(backward_demodulation,[],[f323,f341])).
% 7.19/1.28  fof(f323,plain,(
% 7.19/1.28    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.19/1.28    inference(forward_demodulation,[],[f233,f234])).
% 7.19/1.28  fof(f234,plain,(
% 7.19/1.28    k3_subset_1(u1_struct_0(sK0),sK2) = k4_xboole_0(u1_struct_0(sK0),sK2)),
% 7.19/1.28    inference(unit_resulting_resolution,[],[f76,f101])).
% 7.19/1.28  fof(f101,plain,(
% 7.19/1.28    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.19/1.28    inference(cnf_transformation,[],[f47])).
% 7.19/1.28  fof(f47,plain,(
% 7.19/1.28    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.19/1.28    inference(ennf_transformation,[],[f8])).
% 7.19/1.28  fof(f8,axiom,(
% 7.19/1.28    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.19/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 7.19/1.28  fof(f233,plain,(
% 7.19/1.28    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.19/1.28    inference(unit_resulting_resolution,[],[f76,f100])).
% 7.19/1.28  fof(f100,plain,(
% 7.19/1.28    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.19/1.28    inference(cnf_transformation,[],[f46])).
% 7.19/1.28  fof(f46,plain,(
% 7.19/1.28    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.19/1.28    inference(ennf_transformation,[],[f9])).
% 7.19/1.28  fof(f9,axiom,(
% 7.19/1.28    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 7.19/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 7.19/1.28  fof(f417,plain,(
% 7.19/1.28    v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK2),sK0)),
% 7.19/1.28    inference(backward_demodulation,[],[f324,f341])).
% 7.19/1.28  fof(f324,plain,(
% 7.19/1.28    v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK2),sK0)),
% 7.19/1.28    inference(forward_demodulation,[],[f231,f234])).
% 7.19/1.28  fof(f231,plain,(
% 7.19/1.28    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0)),
% 7.19/1.28    inference(unit_resulting_resolution,[],[f74,f78,f76,f96])).
% 7.19/1.28  fof(f96,plain,(
% 7.19/1.28    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.19/1.28    inference(cnf_transformation,[],[f71])).
% 7.19/1.28  fof(f71,plain,(
% 7.19/1.28    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.19/1.28    inference(nnf_transformation,[],[f42])).
% 7.19/1.28  fof(f42,plain,(
% 7.19/1.28    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.19/1.28    inference(ennf_transformation,[],[f24])).
% 7.19/1.28  fof(f24,axiom,(
% 7.19/1.28    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 7.19/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).
% 7.19/1.28  fof(f78,plain,(
% 7.19/1.28    v2_tops_1(sK2,sK0)),
% 7.19/1.28    inference(cnf_transformation,[],[f67])).
% 7.19/1.28  fof(f419,plain,(
% 7.19/1.28    k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK2)))),
% 7.19/1.28    inference(backward_demodulation,[],[f328,f341])).
% 7.19/1.28  fof(f328,plain,(
% 7.19/1.28    k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK2)))),
% 7.19/1.28    inference(forward_demodulation,[],[f327,f230])).
% 7.19/1.28  fof(f230,plain,(
% 7.19/1.28    k1_xboole_0 = k1_tops_1(sK0,sK2)),
% 7.19/1.28    inference(unit_resulting_resolution,[],[f74,f78,f76,f94])).
% 7.19/1.28  fof(f94,plain,(
% 7.19/1.28    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.19/1.28    inference(cnf_transformation,[],[f70])).
% 7.19/1.28  fof(f327,plain,(
% 7.19/1.28    k1_tops_1(sK0,sK2) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK2)))),
% 7.19/1.28    inference(forward_demodulation,[],[f228,f234])).
% 7.19/1.28  fof(f228,plain,(
% 7.19/1.28    k1_tops_1(sK0,sK2) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))),
% 7.19/1.28    inference(unit_resulting_resolution,[],[f74,f76,f89])).
% 7.19/1.28  fof(f89,plain,(
% 7.19/1.28    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.19/1.28    inference(cnf_transformation,[],[f38])).
% 7.19/1.28  fof(f38,plain,(
% 7.19/1.28    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.19/1.28    inference(ennf_transformation,[],[f22])).
% 7.19/1.28  fof(f22,axiom,(
% 7.19/1.28    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 7.19/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 7.19/1.28  fof(f2662,plain,(
% 7.19/1.28    k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))),
% 7.19/1.28    inference(backward_demodulation,[],[f2328,f2661])).
% 7.19/1.28  fof(f2661,plain,(
% 7.19/1.28    k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK1,sK2)))),
% 7.19/1.28    inference(forward_demodulation,[],[f2660,f1783])).
% 7.19/1.28  fof(f2660,plain,(
% 7.19/1.28    k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK2)) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK1,sK2)))),
% 7.19/1.28    inference(forward_demodulation,[],[f2659,f1382])).
% 7.19/1.28  fof(f1382,plain,(
% 7.19/1.28    k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK1,sK2)) = k9_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),k4_xboole_0(k2_struct_0(sK0),sK2))),
% 7.19/1.28    inference(forward_demodulation,[],[f1381,f1321])).
% 7.19/1.28  fof(f1321,plain,(
% 7.19/1.28    ( ! [X0] : (k7_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),X0) = k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK1,X0))) )),
% 7.19/1.28    inference(forward_demodulation,[],[f1244,f108])).
% 7.19/1.28  fof(f108,plain,(
% 7.19/1.28    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 7.19/1.28    inference(cnf_transformation,[],[f3])).
% 7.19/1.28  fof(f3,axiom,(
% 7.19/1.28    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 7.19/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 7.19/1.28  fof(f1244,plain,(
% 7.19/1.28    ( ! [X0] : (k7_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),X0) = k4_xboole_0(k4_xboole_0(k2_struct_0(sK0),sK1),X0)) )),
% 7.19/1.28    inference(unit_resulting_resolution,[],[f378,f109])).
% 7.19/1.28  fof(f109,plain,(
% 7.19/1.28    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.19/1.28    inference(cnf_transformation,[],[f54])).
% 7.19/1.28  fof(f54,plain,(
% 7.19/1.28    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.19/1.28    inference(ennf_transformation,[],[f13])).
% 7.19/1.28  fof(f13,axiom,(
% 7.19/1.28    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 7.19/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 7.19/1.28  fof(f378,plain,(
% 7.19/1.28    m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 7.19/1.28    inference(backward_demodulation,[],[f214,f341])).
% 7.19/1.28  fof(f214,plain,(
% 7.19/1.28    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.19/1.28    inference(forward_demodulation,[],[f143,f144])).
% 7.19/1.28  fof(f144,plain,(
% 7.19/1.28    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)),
% 7.19/1.28    inference(unit_resulting_resolution,[],[f75,f101])).
% 7.19/1.28  fof(f143,plain,(
% 7.19/1.28    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.19/1.28    inference(unit_resulting_resolution,[],[f75,f100])).
% 7.19/1.28  fof(f1381,plain,(
% 7.19/1.28    k7_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),sK2) = k9_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),k4_xboole_0(k2_struct_0(sK0),sK2))),
% 7.19/1.28    inference(forward_demodulation,[],[f1217,f387])).
% 7.19/1.28  fof(f387,plain,(
% 7.19/1.28    k3_subset_1(k2_struct_0(sK0),sK2) = k4_xboole_0(k2_struct_0(sK0),sK2)),
% 7.19/1.28    inference(backward_demodulation,[],[f234,f341])).
% 7.19/1.28  fof(f1217,plain,(
% 7.19/1.28    k7_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),sK2) = k9_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),k3_subset_1(k2_struct_0(sK0),sK2))),
% 7.19/1.28    inference(unit_resulting_resolution,[],[f345,f378,f103])).
% 7.19/1.28  fof(f103,plain,(
% 7.19/1.28    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.19/1.28    inference(cnf_transformation,[],[f49])).
% 7.19/1.28  fof(f49,plain,(
% 7.19/1.28    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.19/1.28    inference(ennf_transformation,[],[f14])).
% 7.19/1.28  fof(f14,axiom,(
% 7.19/1.28    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 7.19/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 7.19/1.28  fof(f345,plain,(
% 7.19/1.28    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))),
% 7.19/1.28    inference(backward_demodulation,[],[f76,f341])).
% 7.19/1.28  fof(f2659,plain,(
% 7.19/1.28    k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK2)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),k4_xboole_0(k2_struct_0(sK0),sK2)))),
% 7.19/1.28    inference(forward_demodulation,[],[f2640,f1245])).
% 7.19/1.28  fof(f1245,plain,(
% 7.19/1.28    ( ! [X0] : (k9_subset_1(k2_struct_0(sK0),X0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k9_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),X0)) )),
% 7.19/1.28    inference(unit_resulting_resolution,[],[f378,f110])).
% 7.19/1.28  fof(f110,plain,(
% 7.19/1.28    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.19/1.28    inference(cnf_transformation,[],[f55])).
% 7.19/1.28  fof(f55,plain,(
% 7.19/1.28    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.19/1.28    inference(ennf_transformation,[],[f7])).
% 7.19/1.28  fof(f7,axiom,(
% 7.19/1.28    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 7.19/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 7.19/1.28  fof(f2640,plain,(
% 7.19/1.28    k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK2)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK2),k4_xboole_0(k2_struct_0(sK0),sK1)))),
% 7.19/1.28    inference(unit_resulting_resolution,[],[f418,f416,f379,f378,f426])).
% 7.19/1.28  fof(f426,plain,(
% 7.19/1.28    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~v1_tops_1(X1,sK0)) )),
% 7.19/1.28    inference(forward_demodulation,[],[f425,f341])).
% 7.19/1.28  fof(f425,plain,(
% 7.19/1.28    ( ! [X0,X1] : (k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~v1_tops_1(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 7.19/1.28    inference(forward_demodulation,[],[f346,f341])).
% 7.19/1.28  fof(f346,plain,(
% 7.19/1.28    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) | ~v3_pre_topc(X0,sK0) | ~v1_tops_1(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 7.19/1.28    inference(backward_demodulation,[],[f116,f341])).
% 7.19/1.28  fof(f116,plain,(
% 7.19/1.28    ( ! [X0,X1] : (k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_1(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 7.19/1.28    inference(subsumption_resolution,[],[f115,f74])).
% 7.19/1.28  fof(f115,plain,(
% 7.19/1.28    ( ! [X0,X1] : (k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_1(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 7.19/1.28    inference(resolution,[],[f73,f98])).
% 7.19/1.28  fof(f98,plain,(
% 7.19/1.28    ( ! [X2,X0,X1] : (k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.19/1.28    inference(cnf_transformation,[],[f44])).
% 7.19/1.28  fof(f44,plain,(
% 7.19/1.28    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.19/1.28    inference(flattening,[],[f43])).
% 7.19/1.28  fof(f43,plain,(
% 7.19/1.28    ! [X0] : (! [X1] : ((! [X2] : ((k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.19/1.28    inference(ennf_transformation,[],[f28])).
% 7.19/1.28  fof(f28,axiom,(
% 7.19/1.28    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 7.19/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).
% 7.19/1.28  fof(f73,plain,(
% 7.19/1.28    v2_pre_topc(sK0)),
% 7.19/1.28    inference(cnf_transformation,[],[f67])).
% 7.19/1.28  fof(f379,plain,(
% 7.19/1.28    v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)),
% 7.19/1.28    inference(backward_demodulation,[],[f215,f341])).
% 7.19/1.28  fof(f215,plain,(
% 7.19/1.28    v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 7.19/1.28    inference(forward_demodulation,[],[f141,f144])).
% 7.19/1.28  fof(f141,plain,(
% 7.19/1.28    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 7.19/1.28    inference(unit_resulting_resolution,[],[f74,f77,f75,f96])).
% 7.19/1.28  fof(f77,plain,(
% 7.19/1.28    v2_tops_1(sK1,sK0)),
% 7.19/1.28    inference(cnf_transformation,[],[f67])).
% 7.19/1.28  fof(f418,plain,(
% 7.19/1.28    v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK2),sK0)),
% 7.19/1.28    inference(backward_demodulation,[],[f326,f341])).
% 7.19/1.28  fof(f326,plain,(
% 7.19/1.28    v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0)),
% 7.19/1.28    inference(forward_demodulation,[],[f229,f234])).
% 7.19/1.28  fof(f229,plain,(
% 7.19/1.28    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0)),
% 7.19/1.28    inference(unit_resulting_resolution,[],[f74,f79,f76,f92])).
% 7.19/1.28  fof(f92,plain,(
% 7.19/1.28    ( ! [X0,X1] : (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.19/1.28    inference(cnf_transformation,[],[f69])).
% 7.19/1.28  fof(f69,plain,(
% 7.19/1.28    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.19/1.28    inference(nnf_transformation,[],[f40])).
% 7.19/1.28  fof(f40,plain,(
% 7.19/1.28    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.19/1.28    inference(ennf_transformation,[],[f27])).
% 7.19/1.28  fof(f27,axiom,(
% 7.19/1.28    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 7.19/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 7.19/1.28  fof(f79,plain,(
% 7.19/1.28    v4_pre_topc(sK2,sK0)),
% 7.19/1.28    inference(cnf_transformation,[],[f67])).
% 7.19/1.28  fof(f2328,plain,(
% 7.19/1.28    k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK1,sK2))))),
% 7.19/1.28    inference(forward_demodulation,[],[f2295,f890])).
% 7.19/1.28  fof(f890,plain,(
% 7.19/1.28    k3_subset_1(k2_struct_0(sK0),k2_xboole_0(sK1,sK2)) = k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK1,sK2))),
% 7.19/1.28    inference(unit_resulting_resolution,[],[f403,f101])).
% 7.19/1.28  fof(f2295,plain,(
% 7.19/1.28    k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_xboole_0(sK1,sK2))))),
% 7.19/1.28    inference(unit_resulting_resolution,[],[f403,f427])).
% 7.19/1.28  fof(f427,plain,(
% 7.19/1.28    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)))) )),
% 7.19/1.28    inference(forward_demodulation,[],[f347,f341])).
% 7.19/1.28  fof(f347,plain,(
% 7.19/1.28    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) )),
% 7.19/1.28    inference(backward_demodulation,[],[f123,f341])).
% 7.19/1.28  fof(f123,plain,(
% 7.19/1.28    ( ! [X0] : (k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 7.19/1.28    inference(resolution,[],[f74,f89])).
% 7.19/1.28  % SZS output end Proof for theBenchmark
% 7.19/1.28  % (4170)------------------------------
% 7.19/1.28  % (4170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.19/1.28  % (4170)Termination reason: Refutation
% 7.19/1.28  
% 7.19/1.28  % (4170)Memory used [KB]: 3326
% 7.19/1.28  % (4170)Time elapsed: 0.235 s
% 7.19/1.28  % (4170)------------------------------
% 7.19/1.28  % (4170)------------------------------
% 7.19/1.31  % (4131)Success in time 0.943 s
%------------------------------------------------------------------------------
