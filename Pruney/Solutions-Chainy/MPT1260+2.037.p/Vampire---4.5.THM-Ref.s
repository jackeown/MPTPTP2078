%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 871 expanded)
%              Number of leaves         :   16 ( 246 expanded)
%              Depth                    :   35
%              Number of atoms          :  274 (4145 expanded)
%              Number of equality atoms :  105 (1294 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f767,plain,(
    $false ),
    inference(subsumption_resolution,[],[f766,f40])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
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
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(f766,plain,(
    ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f765,f41])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f765,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f754,f183])).

fof(f183,plain,(
    sK1 != k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f182,f39])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f182,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f181,f40])).

fof(f181,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f176,f168])).

fof(f168,plain,(
    ~ v3_pre_topc(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f167])).

fof(f167,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f43,f166])).

fof(f166,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f165,f42])).

fof(f42,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f165,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f164,f40])).

fof(f164,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f163,f41])).

fof(f163,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f47,f155])).

fof(f155,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f154,f39])).

fof(f154,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f152,f40])).

fof(f152,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f147,f41])).

fof(f147,plain,(
    ! [X15,X16] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X16)))
      | sK1 = k1_tops_1(sK0,sK1)
      | ~ v3_pre_topc(sK1,sK0)
      | ~ l1_pre_topc(X16)
      | ~ v2_pre_topc(X16) ) ),
    inference(subsumption_resolution,[],[f144,f40])).

fof(f144,plain,(
    ! [X15,X16] :
      ( ~ v3_pre_topc(sK1,sK0)
      | sK1 = k1_tops_1(sK0,sK1)
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X16)))
      | ~ l1_pre_topc(sK0)
      | ~ l1_pre_topc(X16)
      | ~ v2_pre_topc(X16) ) ),
    inference(resolution,[],[f48,f41])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X3,X1)
      | k1_tops_1(X1,X3) = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f43,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f176,plain,
    ( v3_pre_topc(sK1,sK0)
    | sK1 != k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f162,f41])).

fof(f162,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
      | v3_pre_topc(X15,X14)
      | k1_tops_1(X14,X15) != X15
      | ~ l1_pre_topc(X14)
      | ~ v2_pre_topc(X14) ) ),
    inference(subsumption_resolution,[],[f160,f40])).

fof(f160,plain,(
    ! [X14,X15] :
      ( k1_tops_1(X14,X15) != X15
      | v3_pre_topc(X15,X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
      | ~ l1_pre_topc(sK0)
      | ~ l1_pre_topc(X14)
      | ~ v2_pre_topc(X14) ) ),
    inference(resolution,[],[f49,f41])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | k1_tops_1(X0,X2) != X2
      | v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f754,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f733,f132])).

fof(f132,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X3,k2_tops_1(X2,X3)) = k1_tops_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(duplicate_literal_removal,[],[f127])).

fof(f127,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X3,k2_tops_1(X2,X3)) = k1_tops_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f46,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f733,plain,(
    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f721,f69])).

fof(f69,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f67,f45])).

fof(f45,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f67,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f54,f44])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f721,plain,(
    k5_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f54,f700])).

fof(f700,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f699,f301])).

fof(f301,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,X2)) ),
    inference(backward_demodulation,[],[f233,f290])).

fof(f290,plain,(
    ! [X5] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5) ),
    inference(superposition,[],[f83,f118])).

fof(f118,plain,(
    ! [X4,X3] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X3,X4),X4) ),
    inference(forward_demodulation,[],[f117,f44])).

fof(f117,plain,(
    ! [X4,X3] : k3_xboole_0(k4_xboole_0(X3,X4),X4) = k3_xboole_0(X3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f116,f77])).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f73,f44])).

fof(f73,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f56,f45])).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f116,plain,(
    ! [X4,X3] : k3_xboole_0(k4_xboole_0(X3,X4),X4) = k3_xboole_0(X3,k4_xboole_0(X4,X4)) ),
    inference(forward_demodulation,[],[f115,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f115,plain,(
    ! [X4,X3] : k4_xboole_0(k3_xboole_0(X3,X4),X4) = k3_xboole_0(k4_xboole_0(X3,X4),X4) ),
    inference(forward_demodulation,[],[f109,f54])).

fof(f109,plain,(
    ! [X4,X3] : k4_xboole_0(k3_xboole_0(X3,X4),X4) = k3_xboole_0(k5_xboole_0(X3,k3_xboole_0(X3,X4)),X4) ),
    inference(superposition,[],[f60,f54])).

fof(f60,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f83,plain,(
    ! [X0,X1] : k4_xboole_0(k1_xboole_0,X1) = k3_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f59,f44])).

fof(f233,plain,(
    ! [X2] : k4_xboole_0(k1_xboole_0,X2) = k3_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,X2)) ),
    inference(superposition,[],[f59,f222])).

fof(f222,plain,(
    k1_xboole_0 = k3_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f221,f40])).

fof(f221,plain,
    ( k1_xboole_0 = k3_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f219,f41])).

fof(f219,plain,
    ( k1_xboole_0 = k3_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f215,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f215,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = k3_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f208,f168])).

fof(f208,plain,
    ( k1_xboole_0 = k3_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f118,f98])).

fof(f98,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f62,f42])).

fof(f699,plain,(
    k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k3_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f698,f583])).

fof(f583,plain,(
    ! [X7] : k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k3_xboole_0(k3_xboole_0(sK1,k2_tops_1(sK0,sK1)),X7) ),
    inference(forward_demodulation,[],[f582,f225])).

fof(f225,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f65,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f53,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f582,plain,(
    ! [X7] : k3_xboole_0(k2_tops_1(sK0,sK1),sK1) = k3_xboole_0(k3_xboole_0(k2_tops_1(sK0,sK1),sK1),X7) ),
    inference(forward_demodulation,[],[f543,f45])).

fof(f543,plain,(
    ! [X7] : k3_xboole_0(k3_xboole_0(k2_tops_1(sK0,sK1),sK1),X7) = k4_xboole_0(k3_xboole_0(k2_tops_1(sK0,sK1),sK1),k1_xboole_0) ),
    inference(superposition,[],[f88,f301])).

fof(f88,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(superposition,[],[f56,f59])).

fof(f698,plain,(
    ! [X13] : k3_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k1_xboole_0)) = k3_xboole_0(k3_xboole_0(sK1,k2_tops_1(sK0,sK1)),X13) ),
    inference(forward_demodulation,[],[f653,f225])).

fof(f653,plain,(
    ! [X13] : k3_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k1_xboole_0)) = k3_xboole_0(k3_xboole_0(k2_tops_1(sK0,sK1),sK1),X13) ),
    inference(superposition,[],[f94,f301])).

fof(f94,plain,(
    ! [X10,X8,X9] : k3_xboole_0(k3_xboole_0(X8,X9),X10) = k3_xboole_0(X8,k4_xboole_0(X9,k3_xboole_0(X8,k4_xboole_0(X9,X10)))) ),
    inference(forward_demodulation,[],[f87,f59])).

fof(f87,plain,(
    ! [X10,X8,X9] : k3_xboole_0(k3_xboole_0(X8,X9),X10) = k3_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(k3_xboole_0(X8,X9),X10))) ),
    inference(superposition,[],[f59,f56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:52:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (18996)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (18994)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (18993)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (19010)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (18998)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (18997)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (18999)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (19005)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (19003)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (19001)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (19000)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (18995)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (19008)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (19009)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (19004)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (19007)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (19002)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (19006)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.51  % (18996)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f767,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f766,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 0.21/0.51    inference(negated_conjecture,[],[f19])).
% 0.21/0.51  fof(f19,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).
% 0.21/0.51  fof(f766,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f765,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f765,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f754,f183])).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    sK1 != k1_tops_1(sK0,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f182,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    v2_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f182,plain,(
% 0.21/0.51    sK1 != k1_tops_1(sK0,sK1) | ~v2_pre_topc(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f181,f40])).
% 0.21/0.51  fof(f181,plain,(
% 0.21/0.51    sK1 != k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f176,f168])).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    ~v3_pre_topc(sK1,sK0)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f167])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.21/0.51    inference(backward_demodulation,[],[f43,f166])).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f165,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f164,f40])).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~v3_pre_topc(sK1,sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f163,f41])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v3_pre_topc(sK1,sK0)),
% 0.21/0.51    inference(superposition,[],[f47,f155])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f154,f39])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f152,f40])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.51    inference(resolution,[],[f147,f41])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    ( ! [X15,X16] : (~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X16))) | sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | ~l1_pre_topc(X16) | ~v2_pre_topc(X16)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f144,f40])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    ( ! [X15,X16] : (~v3_pre_topc(sK1,sK0) | sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X16))) | ~l1_pre_topc(sK0) | ~l1_pre_topc(X16) | ~v2_pre_topc(X16)) )),
% 0.21/0.51    inference(resolution,[],[f48,f41])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1) | k1_tops_1(X1,X3) = X3 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    v3_pre_topc(sK1,sK0) | sK1 != k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.51    inference(resolution,[],[f162,f41])).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    ( ! [X14,X15] : (~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14))) | v3_pre_topc(X15,X14) | k1_tops_1(X14,X15) != X15 | ~l1_pre_topc(X14) | ~v2_pre_topc(X14)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f160,f40])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    ( ! [X14,X15] : (k1_tops_1(X14,X15) != X15 | v3_pre_topc(X15,X14) | ~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14))) | ~l1_pre_topc(sK0) | ~l1_pre_topc(X14) | ~v2_pre_topc(X14)) )),
% 0.21/0.51    inference(resolution,[],[f49,f41])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | k1_tops_1(X0,X2) != X2 | v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f754,plain,(
% 0.21/0.51    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.21/0.51    inference(superposition,[],[f733,f132])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    ( ! [X2,X3] : (k4_xboole_0(X3,k2_tops_1(X2,X3)) = k1_tops_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f127])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    ( ! [X2,X3] : (k4_xboole_0(X3,k2_tops_1(X2,X3)) = k1_tops_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 0.21/0.51    inference(superposition,[],[f46,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 0.21/0.51  fof(f733,plain,(
% 0.21/0.51    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.51    inference(forward_demodulation,[],[f721,f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(forward_demodulation,[],[f67,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(superposition,[],[f54,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.51  fof(f721,plain,(
% 0.21/0.51    k5_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.51    inference(superposition,[],[f54,f700])).
% 0.21/0.51  fof(f700,plain,(
% 0.21/0.51    k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.51    inference(forward_demodulation,[],[f699,f301])).
% 0.21/0.51  fof(f301,plain,(
% 0.21/0.51    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,X2))) )),
% 0.21/0.51    inference(backward_demodulation,[],[f233,f290])).
% 0.21/0.51  fof(f290,plain,(
% 0.21/0.51    ( ! [X5] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5)) )),
% 0.21/0.51    inference(superposition,[],[f83,f118])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    ( ! [X4,X3] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X3,X4),X4)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f117,f44])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    ( ! [X4,X3] : (k3_xboole_0(k4_xboole_0(X3,X4),X4) = k3_xboole_0(X3,k1_xboole_0)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f116,f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f73,f44])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 0.21/0.51    inference(superposition,[],[f56,f45])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    ( ! [X4,X3] : (k3_xboole_0(k4_xboole_0(X3,X4),X4) = k3_xboole_0(X3,k4_xboole_0(X4,X4))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f115,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    ( ! [X4,X3] : (k4_xboole_0(k3_xboole_0(X3,X4),X4) = k3_xboole_0(k4_xboole_0(X3,X4),X4)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f109,f54])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    ( ! [X4,X3] : (k4_xboole_0(k3_xboole_0(X3,X4),X4) = k3_xboole_0(k5_xboole_0(X3,k3_xboole_0(X3,X4)),X4)) )),
% 0.21/0.51    inference(superposition,[],[f60,f54])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(k1_xboole_0,X1) = k3_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))) )),
% 0.21/0.51    inference(superposition,[],[f59,f44])).
% 0.21/0.51  fof(f233,plain,(
% 0.21/0.51    ( ! [X2] : (k4_xboole_0(k1_xboole_0,X2) = k3_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,X2))) )),
% 0.21/0.51    inference(superposition,[],[f59,f222])).
% 0.21/0.51  fof(f222,plain,(
% 0.21/0.51    k1_xboole_0 = k3_xboole_0(k2_tops_1(sK0,sK1),sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f221,f40])).
% 0.21/0.51  fof(f221,plain,(
% 0.21/0.51    k1_xboole_0 = k3_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f219,f41])).
% 0.21/0.51  fof(f219,plain,(
% 0.21/0.51    k1_xboole_0 = k3_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.21/0.51    inference(resolution,[],[f215,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.21/0.51  fof(f215,plain,(
% 0.21/0.51    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k3_xboole_0(k2_tops_1(sK0,sK1),sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f208,f168])).
% 0.21/0.51  fof(f208,plain,(
% 0.21/0.51    k1_xboole_0 = k3_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)),
% 0.21/0.51    inference(superposition,[],[f118,f98])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)),
% 0.21/0.51    inference(superposition,[],[f62,f42])).
% 0.21/0.51  fof(f699,plain,(
% 0.21/0.51    k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k3_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k1_xboole_0))),
% 0.21/0.51    inference(forward_demodulation,[],[f698,f583])).
% 0.21/0.51  fof(f583,plain,(
% 0.21/0.51    ( ! [X7] : (k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k3_xboole_0(k3_xboole_0(sK1,k2_tops_1(sK0,sK1)),X7)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f582,f225])).
% 0.21/0.51  fof(f225,plain,(
% 0.21/0.51    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 0.21/0.51    inference(superposition,[],[f65,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 0.21/0.51    inference(superposition,[],[f53,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.51  fof(f582,plain,(
% 0.21/0.51    ( ! [X7] : (k3_xboole_0(k2_tops_1(sK0,sK1),sK1) = k3_xboole_0(k3_xboole_0(k2_tops_1(sK0,sK1),sK1),X7)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f543,f45])).
% 0.21/0.51  fof(f543,plain,(
% 0.21/0.51    ( ! [X7] : (k3_xboole_0(k3_xboole_0(k2_tops_1(sK0,sK1),sK1),X7) = k4_xboole_0(k3_xboole_0(k2_tops_1(sK0,sK1),sK1),k1_xboole_0)) )),
% 0.21/0.51    inference(superposition,[],[f88,f301])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))) )),
% 0.21/0.51    inference(superposition,[],[f56,f59])).
% 0.21/0.51  fof(f698,plain,(
% 0.21/0.51    ( ! [X13] : (k3_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k1_xboole_0)) = k3_xboole_0(k3_xboole_0(sK1,k2_tops_1(sK0,sK1)),X13)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f653,f225])).
% 0.21/0.51  fof(f653,plain,(
% 0.21/0.51    ( ! [X13] : (k3_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k1_xboole_0)) = k3_xboole_0(k3_xboole_0(k2_tops_1(sK0,sK1),sK1),X13)) )),
% 0.21/0.51    inference(superposition,[],[f94,f301])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ( ! [X10,X8,X9] : (k3_xboole_0(k3_xboole_0(X8,X9),X10) = k3_xboole_0(X8,k4_xboole_0(X9,k3_xboole_0(X8,k4_xboole_0(X9,X10))))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f87,f59])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X10,X8,X9] : (k3_xboole_0(k3_xboole_0(X8,X9),X10) = k3_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(k3_xboole_0(X8,X9),X10)))) )),
% 0.21/0.51    inference(superposition,[],[f59,f56])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (18996)------------------------------
% 0.21/0.51  % (18996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (18996)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (18996)Memory used [KB]: 2302
% 0.21/0.51  % (18996)Time elapsed: 0.103 s
% 0.21/0.51  % (18996)------------------------------
% 0.21/0.51  % (18996)------------------------------
% 0.21/0.51  % (18992)Success in time 0.155 s
%------------------------------------------------------------------------------
