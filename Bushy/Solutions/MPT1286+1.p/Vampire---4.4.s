%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t108_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:26 EDT 2019

% Result     : Theorem 31.62s
% Output     : Refutation 31.62s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 939 expanded)
%              Number of leaves         :   13 ( 173 expanded)
%              Depth                    :   19
%              Number of atoms          :  321 (4067 expanded)
%              Number of equality atoms :   67 ( 274 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f79374,plain,(
    $false ),
    inference(subsumption_resolution,[],[f79373,f32467])).

fof(f32467,plain,(
    ~ r1_tarski(k2_xboole_0(sK1,sK2),k2_pre_topc(sK0,k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) ),
    inference(subsumption_resolution,[],[f32464,f10022])).

fof(f10022,plain,(
    k2_xboole_0(sK1,sK2) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f10008,f544])).

fof(f544,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_pre_topc(sK0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(subsumption_resolution,[],[f543,f82])).

fof(f82,plain,(
    ~ v5_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v5_tops_1(X2,X0)
              & v5_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v5_tops_1(X2,X0)
              & v5_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v5_tops_1(X2,X0)
                    & v5_tops_1(X1,X0) )
                 => v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v5_tops_1(X2,X0)
                  & v5_tops_1(X1,X0) )
               => v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t108_tops_1.p',t108_tops_1)).

fof(f543,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_pre_topc(sK0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | v5_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f524,f85])).

fof(f85,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f524,plain,
    ( ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_pre_topc(sK0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | v5_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(resolution,[],[f201,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1
      | v5_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t108_tops_1.p',d7_tops_1)).

fof(f201,plain,(
    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f161,f79])).

fof(f79,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f161,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,X2),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f83,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t108_tops_1.p',dt_k4_subset_1)).

fof(f83,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f10008,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(backward_demodulation,[],[f10007,f211])).

fof(f211,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) ),
    inference(resolution,[],[f137,f83])).

fof(f137,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),X4,sK2) = k4_subset_1(u1_struct_0(sK0),sK2,X4) ) ),
    inference(resolution,[],[f79,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t108_tops_1.p',commutativity_k4_subset_1)).

fof(f10007,plain,(
    k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f7228,f99])).

fof(f99,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t108_tops_1.p',commutativity_k2_xboole_0)).

fof(f7228,plain,(
    k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f136,f83])).

fof(f136,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),sK2,X3) = k2_xboole_0(sK2,X3) ) ),
    inference(resolution,[],[f79,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t108_tops_1.p',redefinition_k4_subset_1)).

fof(f32464,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,sK2),k2_pre_topc(sK0,k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
    | k2_xboole_0(sK1,sK2) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f32463,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t108_tops_1.p',d10_xboole_0)).

fof(f32463,plain,(
    r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f32462,f10011])).

fof(f10011,plain,(
    k2_xboole_0(sK1,sK2) = k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f10008,f479])).

fof(f479,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(forward_demodulation,[],[f461,f211])).

fof(f461,plain,(
    k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(backward_demodulation,[],[f454,f334])).

fof(f334,plain,(
    k4_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(backward_demodulation,[],[f312,f259])).

fof(f259,plain,(
    k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(forward_demodulation,[],[f254,f211])).

fof(f254,plain,(
    k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK1)) ),
    inference(resolution,[],[f141,f83])).

fof(f141,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f140,f84])).

fof(f84,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f140,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f125,f85])).

fof(f125,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,X0)) ) ),
    inference(resolution,[],[f79,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) = k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) = k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) = k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) = k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t108_tops_1.p',t50_pre_topc)).

fof(f312,plain,(
    k2_pre_topc(sK0,sK2) = sK2 ),
    inference(forward_demodulation,[],[f311,f124])).

fof(f124,plain,(
    k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2 ),
    inference(subsumption_resolution,[],[f123,f85])).

fof(f123,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f122,f79])).

fof(f122,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f81,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f81,plain,(
    v5_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f311,plain,(
    k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f286,f85])).

fof(f286,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) ),
    inference(resolution,[],[f149,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t108_tops_1.p',projectivity_k2_pre_topc)).

fof(f149,plain,(
    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f133,f85])).

fof(f133,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f79,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t108_tops_1.p',dt_k1_tops_1)).

fof(f454,plain,(
    k2_pre_topc(sK0,sK1) = sK1 ),
    inference(forward_demodulation,[],[f453,f121])).

fof(f121,plain,(
    k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(subsumption_resolution,[],[f120,f85])).

fof(f120,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f119,f83])).

fof(f119,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f80,f93])).

fof(f80,plain,(
    v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f453,plain,(
    k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f427,f85])).

fof(f427,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f175,f102])).

fof(f175,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f159,f85])).

fof(f159,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f83,f112])).

fof(f32462,plain,(
    r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_xboole_0(sK1,sK2))),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f32461,f85])).

fof(f32461,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_xboole_0(sK1,sK2))),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f32460,f10010])).

fof(f10010,plain,(
    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f10008,f201])).

fof(f32460,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_xboole_0(sK1,sK2))),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f11546,f10026])).

fof(f10026,plain,(
    m1_subset_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f10008,f554])).

fof(f554,plain,(
    m1_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f530,f85])).

fof(f530,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f201,f112])).

fof(f11546,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_pre_topc(X0,k1_tops_1(sK0,k2_xboole_0(sK1,sK2))),k2_pre_topc(X0,k2_xboole_0(sK1,sK2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(forward_demodulation,[],[f11545,f10008])).

fof(f11545,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_pre_topc(X0,k1_tops_1(sK0,k2_xboole_0(sK1,sK2))),k2_pre_topc(X0,k2_xboole_0(sK1,sK2)))
      | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(forward_demodulation,[],[f10072,f10008])).

fof(f10072,plain,(
    ! [X0] :
      ( r1_tarski(k2_pre_topc(X0,k1_tops_1(sK0,k2_xboole_0(sK1,sK2))),k2_pre_topc(X0,k2_xboole_0(sK1,sK2)))
      | ~ m1_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(backward_demodulation,[],[f10008,f981])).

fof(f981,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k2_pre_topc(X0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))),k2_pre_topc(X0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ) ),
    inference(resolution,[],[f552,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t108_tops_1.p',t49_pre_topc)).

fof(f552,plain,(
    r1_tarski(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(subsumption_resolution,[],[f528,f85])).

fof(f528,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(resolution,[],[f201,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t108_tops_1.p',t44_tops_1)).

fof(f79373,plain,(
    r1_tarski(k2_xboole_0(sK1,sK2),k2_pre_topc(sK0,k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) ),
    inference(forward_demodulation,[],[f79372,f10130])).

fof(f10130,plain,(
    k2_xboole_0(sK1,sK2) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f10008,f1899])).

fof(f1899,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(forward_demodulation,[],[f1898,f211])).

fof(f1898,plain,(
    k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(forward_demodulation,[],[f1897,f121])).

fof(f1897,plain,(
    k4_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(forward_demodulation,[],[f1866,f1720])).

fof(f1720,plain,(
    k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f294,f175])).

fof(f294,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),X4,k1_tops_1(sK0,sK2)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),X4) ) ),
    inference(resolution,[],[f149,f86])).

fof(f1866,plain,(
    k4_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f302,f175])).

fof(f302,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),X0)) ) ),
    inference(forward_demodulation,[],[f301,f124])).

fof(f301,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),X0)) ) ),
    inference(subsumption_resolution,[],[f300,f84])).

fof(f300,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),X0)) ) ),
    inference(subsumption_resolution,[],[f282,f85])).

fof(f282,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),X0)) ) ),
    inference(resolution,[],[f149,f90])).

fof(f79372,plain,(
    r1_tarski(k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) ),
    inference(subsumption_resolution,[],[f79371,f85])).

fof(f79371,plain,
    ( r1_tarski(k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f79370,f10026])).

fof(f79370,plain,
    ( r1_tarski(k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
    | ~ m1_subset_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f11551,f1341])).

fof(f1341,plain,(
    m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f433,f149])).

fof(f433,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X2),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f175,f88])).

fof(f11551,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_pre_topc(X0,k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),k2_pre_topc(X0,k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
      | ~ m1_subset_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(forward_demodulation,[],[f10102,f10008])).

fof(f10102,plain,(
    ! [X0] :
      ( r1_tarski(k2_pre_topc(X0,k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),k2_pre_topc(X0,k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
      | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(backward_demodulation,[],[f10008,f1653])).

fof(f1653,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k2_pre_topc(X0,k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),k2_pre_topc(X0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))) ) ),
    inference(resolution,[],[f650,f104])).

fof(f650,plain,(
    r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(resolution,[],[f168,f79])).

fof(f168,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X1)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X1))) ) ),
    inference(subsumption_resolution,[],[f152,f85])).

fof(f152,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X1)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X1))) ) ),
    inference(resolution,[],[f83,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t108_tops_1.p',t49_tops_1)).
%------------------------------------------------------------------------------
