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
% DateTime   : Thu Dec  3 13:07:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 274 expanded)
%              Number of leaves         :   13 ( 111 expanded)
%              Depth                    :   24
%              Number of atoms          :  307 (1716 expanded)
%              Number of equality atoms :    9 (  19 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f166,plain,(
    $false ),
    inference(resolution,[],[f165,f31])).

fof(f31,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r1_tarski(k5_setfam_1(sK0,sK3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f26,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3))))
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_setfam_1(sK0,X3),k5_setfam_1(sK0,k6_funct_2(sK0,X1,X2,k7_funct_2(sK0,X1,X2,X3))))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
              & v1_funct_2(X2,sK0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k5_setfam_1(sK0,X3),k5_setfam_1(sK0,k6_funct_2(sK0,X1,X2,k7_funct_2(sK0,X1,X2,X3))))
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
            & v1_funct_2(X2,sK0,X1)
            & v1_funct_1(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k5_setfam_1(sK0,X3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,X2,k7_funct_2(sK0,sK1,X2,X3))))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X2,sK0,sK1)
          & v1_funct_1(X2) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k5_setfam_1(sK0,X3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,X2,k7_funct_2(sK0,sK1,X2,X3))))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X2,sK0,sK1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k5_setfam_1(sK0,X3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,X3))))
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k5_setfam_1(sK0,X3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,X3))))
        & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( ~ r1_tarski(k5_setfam_1(sK0,sK3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))))
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3))))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3))))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
                   => r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)))) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
                 => r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t184_funct_2)).

fof(f165,plain,(
    v1_xboole_0(sK0) ),
    inference(resolution,[],[f163,f32])).

fof(f32,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f163,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f161,f61])).

fof(f61,plain,(
    m1_subset_1(k3_tarski(sK3),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f59,f54])).

fof(f54,plain,(
    k5_setfam_1(sK0,sK3) = k3_tarski(sK3) ),
    inference(resolution,[],[f40,f36])).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f59,plain,(
    m1_subset_1(k5_setfam_1(sK0,sK3),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f41,f36])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(f161,plain,
    ( ~ m1_subset_1(k3_tarski(sK3),k1_zfmisc_1(sK0))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f157,f35])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f157,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(k3_tarski(sK3),k1_zfmisc_1(sK0))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f156,f36])).

fof(f156,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(k3_tarski(sK3),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f154,f68])).

fof(f68,plain,(
    ! [X0] : m1_setfam_1(X0,k3_tarski(X0)) ),
    inference(resolution,[],[f67,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(X1))
      | m1_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
        | ~ r1_tarski(X0,k3_tarski(X1)) )
      & ( r1_tarski(X0,k3_tarski(X1))
        | ~ m1_setfam_1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
    <=> r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

fof(f67,plain,(
    ! [X0] : r1_tarski(k3_tarski(X0),k3_tarski(X0)) ),
    inference(resolution,[],[f65,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k3_tarski(X0),k1_zfmisc_1(k3_tarski(X0))) ),
    inference(forward_demodulation,[],[f63,f57])).

fof(f57,plain,(
    ! [X0] : k3_tarski(X0) = k5_setfam_1(k3_tarski(X0),X0) ),
    inference(resolution,[],[f55,f38])).

fof(f38,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_zfmisc_1(X1))
      | k3_tarski(X0) = k5_setfam_1(X1,X0) ) ),
    inference(resolution,[],[f40,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k5_setfam_1(k3_tarski(X0),X0),k1_zfmisc_1(k3_tarski(X0))) ),
    inference(resolution,[],[f60,f38])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f41,f47])).

fof(f154,plain,
    ( ~ m1_setfam_1(sK3,k3_tarski(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(k3_tarski(sK3),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f153,f34])).

fof(f34,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f153,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(k3_tarski(sK3),k1_zfmisc_1(sK0))
    | ~ m1_setfam_1(sK3,k3_tarski(sK3))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f152,f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_setfam_1(k6_funct_2(X2,X3,sK2,k7_funct_2(X2,X3,sK2,X0)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(sK2,X2,X3)
      | ~ m1_setfam_1(X0,X1)
      | v1_xboole_0(X3)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f39,f33])).

fof(f33,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_setfam_1(X3,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | m1_setfam_1(k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)),X4)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( m1_setfam_1(k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)),X4)
                      | ~ m1_setfam_1(X3,X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( m1_setfam_1(k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)),X4)
                      | ~ m1_setfam_1(X3,X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(X0))
                     => ( m1_setfam_1(X3,X4)
                       => m1_setfam_1(k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_funct_2)).

fof(f152,plain,(
    ~ m1_setfam_1(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)),k3_tarski(sK3)) ),
    inference(resolution,[],[f151,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ m1_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f151,plain,(
    ~ r1_tarski(k3_tarski(sK3),k3_tarski(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)))) ),
    inference(backward_demodulation,[],[f56,f147])).

fof(f147,plain,(
    k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))) = k3_tarski(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))) ),
    inference(resolution,[],[f146,f31])).

fof(f146,plain,
    ( v1_xboole_0(sK0)
    | k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))) = k3_tarski(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))) ),
    inference(resolution,[],[f111,f32])).

fof(f111,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))) = k3_tarski(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))) ),
    inference(resolution,[],[f104,f40])).

fof(f104,plain,
    ( m1_subset_1(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,
    ( m1_subset_1(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f100,f82])).

fof(f82,plain,
    ( m1_subset_1(k7_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f79,f36])).

fof(f79,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | m1_subset_1(k7_funct_2(sK0,sK1,sK2,X0),k1_zfmisc_1(k1_zfmisc_1(sK1)))
      | v1_xboole_0(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f77,f35])).

% (27052)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
fof(f77,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | m1_subset_1(k7_funct_2(sK0,sK1,sK2,X0),k1_zfmisc_1(k1_zfmisc_1(sK1)))
      | v1_xboole_0(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f76,f34])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(sK2,X1,X2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | m1_subset_1(k7_funct_2(X1,X2,sK2,X0),k1_zfmisc_1(k1_zfmisc_1(X2)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f48,f33])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_funct_2)).

fof(f100,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1)))
      | m1_subset_1(k6_funct_2(sK0,sK1,sK2,X0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | v1_xboole_0(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f98,f35])).

fof(f98,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1)))
      | m1_subset_1(k6_funct_2(sK0,sK1,sK2,X0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | v1_xboole_0(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f78,f34])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(sK2,X2,X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | m1_subset_1(k6_funct_2(X2,X1,sK2,X0),k1_zfmisc_1(k1_zfmisc_1(X2)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f49,f33])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_funct_2)).

fof(f56,plain,(
    ~ r1_tarski(k3_tarski(sK3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)))) ),
    inference(backward_demodulation,[],[f37,f54])).

fof(f37,plain,(
    ~ r1_tarski(k5_setfam_1(sK0,sK3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)))) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:39:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.46  % (27059)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.47  % (27051)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.47  % (27059)Refutation not found, incomplete strategy% (27059)------------------------------
% 0.20/0.47  % (27059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (27059)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (27059)Memory used [KB]: 10490
% 0.20/0.47  % (27059)Time elapsed: 0.060 s
% 0.20/0.47  % (27059)------------------------------
% 0.20/0.47  % (27059)------------------------------
% 0.20/0.48  % (27064)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.49  % (27056)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (27060)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.49  % (27072)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.50  % (27072)Refutation not found, incomplete strategy% (27072)------------------------------
% 0.20/0.50  % (27072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (27072)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (27072)Memory used [KB]: 10618
% 0.20/0.50  % (27072)Time elapsed: 0.055 s
% 0.20/0.50  % (27072)------------------------------
% 0.20/0.50  % (27072)------------------------------
% 0.20/0.50  % (27055)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.50  % (27053)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.50  % (27058)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.50  % (27058)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f166,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(resolution,[],[f165,f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ~v1_xboole_0(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    (((~r1_tarski(k5_setfam_1(sK0,sK3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f26,f25,f24,f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_setfam_1(sK0,X3),k5_setfam_1(sK0,k6_funct_2(sK0,X1,X2,k7_funct_2(sK0,X1,X2,X3)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) & v1_funct_2(X2,sK0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_setfam_1(sK0,X3),k5_setfam_1(sK0,k6_funct_2(sK0,X1,X2,k7_funct_2(sK0,X1,X2,X3)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) & v1_funct_2(X2,sK0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k5_setfam_1(sK0,X3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,X2,k7_funct_2(sK0,sK1,X2,X3)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X2,sK0,sK1) & v1_funct_1(X2)) & ~v1_xboole_0(sK1))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ? [X2] : (? [X3] : (~r1_tarski(k5_setfam_1(sK0,X3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,X2,k7_funct_2(sK0,sK1,X2,X3)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X2,sK0,sK1) & v1_funct_1(X2)) => (? [X3] : (~r1_tarski(k5_setfam_1(sK0,X3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,X3)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ? [X3] : (~r1_tarski(k5_setfam_1(sK0,X3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,X3)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (~r1_tarski(k5_setfam_1(sK0,sK3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.50    inference(flattening,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,negated_conjecture,(
% 0.20/0.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) => r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3))))))))),
% 0.20/0.50    inference(negated_conjecture,[],[f10])).
% 0.20/0.50  fof(f10,conjecture,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) => r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3))))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t184_funct_2)).
% 0.20/0.50  fof(f165,plain,(
% 0.20/0.50    v1_xboole_0(sK0)),
% 0.20/0.50    inference(resolution,[],[f163,f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ~v1_xboole_0(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f163,plain,(
% 0.20/0.50    v1_xboole_0(sK1) | v1_xboole_0(sK0)),
% 0.20/0.50    inference(resolution,[],[f161,f61])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    m1_subset_1(k3_tarski(sK3),k1_zfmisc_1(sK0))),
% 0.20/0.50    inference(forward_demodulation,[],[f59,f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    k5_setfam_1(sK0,sK3) = k3_tarski(sK3)),
% 0.20/0.50    inference(resolution,[],[f40,f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k3_tarski(X1) = k5_setfam_1(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k3_tarski(X1) = k5_setfam_1(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    m1_subset_1(k5_setfam_1(sK0,sK3),k1_zfmisc_1(sK0))),
% 0.20/0.50    inference(resolution,[],[f41,f36])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).
% 0.20/0.50  fof(f161,plain,(
% 0.20/0.50    ~m1_subset_1(k3_tarski(sK3),k1_zfmisc_1(sK0)) | v1_xboole_0(sK1) | v1_xboole_0(sK0)),
% 0.20/0.50    inference(resolution,[],[f157,f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f157,plain,(
% 0.20/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(k3_tarski(sK3),k1_zfmisc_1(sK0)) | v1_xboole_0(sK1) | v1_xboole_0(sK0)),
% 0.20/0.50    inference(resolution,[],[f156,f36])).
% 0.20/0.50  fof(f156,plain,(
% 0.20/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(k3_tarski(sK3),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK1) | v1_xboole_0(sK0)),
% 0.20/0.50    inference(resolution,[],[f154,f68])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    ( ! [X0] : (m1_setfam_1(X0,k3_tarski(X0))) )),
% 0.20/0.50    inference(resolution,[],[f67,f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X0,k3_tarski(X1)) | m1_setfam_1(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0,X1] : ((m1_setfam_1(X1,X0) | ~r1_tarski(X0,k3_tarski(X1))) & (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)))),
% 0.20/0.50    inference(nnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_setfam_1(X1,X0) <=> r1_tarski(X0,k3_tarski(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(k3_tarski(X0),k3_tarski(X0))) )),
% 0.20/0.50    inference(resolution,[],[f65,f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.50    inference(nnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k3_tarski(X0),k1_zfmisc_1(k3_tarski(X0)))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f63,f57])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X0] : (k3_tarski(X0) = k5_setfam_1(k3_tarski(X0),X0)) )),
% 0.20/0.50    inference(resolution,[],[f55,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X0,k1_zfmisc_1(X1)) | k3_tarski(X0) = k5_setfam_1(X1,X0)) )),
% 0.20/0.50    inference(resolution,[],[f40,f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k5_setfam_1(k3_tarski(X0),X0),k1_zfmisc_1(k3_tarski(X0)))) )),
% 0.20/0.50    inference(resolution,[],[f60,f38])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X1,k1_zfmisc_1(X0)) | m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(resolution,[],[f41,f47])).
% 0.20/0.50  fof(f154,plain,(
% 0.20/0.50    ~m1_setfam_1(sK3,k3_tarski(sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(k3_tarski(sK3),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK0))) | v1_xboole_0(sK1) | v1_xboole_0(sK0)),
% 0.20/0.50    inference(resolution,[],[f153,f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f153,plain,(
% 0.20/0.50    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(k3_tarski(sK3),k1_zfmisc_1(sK0)) | ~m1_setfam_1(sK3,k3_tarski(sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK0)),
% 0.20/0.50    inference(resolution,[],[f152,f91])).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (m1_setfam_1(k6_funct_2(X2,X3,sK2,k7_funct_2(X2,X3,sK2,X0)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X2))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(sK2,X2,X3) | ~m1_setfam_1(X0,X1) | v1_xboole_0(X3) | v1_xboole_0(X2)) )),
% 0.20/0.50    inference(resolution,[],[f39,f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    v1_funct_1(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_setfam_1(X3,X4) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | m1_setfam_1(k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)),X4) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (m1_setfam_1(k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)),X4) | ~m1_setfam_1(X3,X4) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.50    inference(flattening,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((m1_setfam_1(k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)),X4) | ~m1_setfam_1(X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X0)) => (m1_setfam_1(X3,X4) => m1_setfam_1(k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)),X4)))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_funct_2)).
% 0.20/0.50  fof(f152,plain,(
% 0.20/0.50    ~m1_setfam_1(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)),k3_tarski(sK3))),
% 0.20/0.50    inference(resolution,[],[f151,f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f151,plain,(
% 0.20/0.50    ~r1_tarski(k3_tarski(sK3),k3_tarski(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))))),
% 0.20/0.50    inference(backward_demodulation,[],[f56,f147])).
% 0.20/0.50  fof(f147,plain,(
% 0.20/0.50    k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))) = k3_tarski(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)))),
% 0.20/0.50    inference(resolution,[],[f146,f31])).
% 0.20/0.50  fof(f146,plain,(
% 0.20/0.50    v1_xboole_0(sK0) | k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))) = k3_tarski(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)))),
% 0.20/0.50    inference(resolution,[],[f111,f32])).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    v1_xboole_0(sK1) | v1_xboole_0(sK0) | k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))) = k3_tarski(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)))),
% 0.20/0.50    inference(resolution,[],[f104,f40])).
% 0.20/0.50  fof(f104,plain,(
% 0.20/0.50    m1_subset_1(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(sK0))) | v1_xboole_0(sK1) | v1_xboole_0(sK0)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f103])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    m1_subset_1(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(sK0))) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | v1_xboole_0(sK1) | v1_xboole_0(sK0)),
% 0.20/0.50    inference(resolution,[],[f100,f82])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    m1_subset_1(k7_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK1))) | v1_xboole_0(sK1) | v1_xboole_0(sK0)),
% 0.20/0.50    inference(resolution,[],[f79,f36])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | m1_subset_1(k7_funct_2(sK0,sK1,sK2,X0),k1_zfmisc_1(k1_zfmisc_1(sK1))) | v1_xboole_0(sK1) | v1_xboole_0(sK0)) )),
% 0.20/0.50    inference(resolution,[],[f77,f35])).
% 0.20/0.50  % (27052)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | m1_subset_1(k7_funct_2(sK0,sK1,sK2,X0),k1_zfmisc_1(k1_zfmisc_1(sK1))) | v1_xboole_0(sK1) | v1_xboole_0(sK0)) )),
% 0.20/0.50    inference(resolution,[],[f76,f34])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v1_funct_2(sK2,X1,X2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) | m1_subset_1(k7_funct_2(X1,X2,sK2,X0),k1_zfmisc_1(k1_zfmisc_1(X2))) | v1_xboole_0(X2) | v1_xboole_0(X1)) )),
% 0.20/0.50    inference(resolution,[],[f48,f33])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.20/0.50    inference(flattening,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_funct_2)).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) | m1_subset_1(k6_funct_2(sK0,sK1,sK2,X0),k1_zfmisc_1(k1_zfmisc_1(sK0))) | v1_xboole_0(sK1) | v1_xboole_0(sK0)) )),
% 0.20/0.50    inference(resolution,[],[f98,f35])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) | m1_subset_1(k6_funct_2(sK0,sK1,sK2,X0),k1_zfmisc_1(k1_zfmisc_1(sK0))) | v1_xboole_0(sK1) | v1_xboole_0(sK0)) )),
% 0.20/0.50    inference(resolution,[],[f78,f34])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v1_funct_2(sK2,X2,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) | m1_subset_1(k6_funct_2(X2,X1,sK2,X0),k1_zfmisc_1(k1_zfmisc_1(X2))) | v1_xboole_0(X1) | v1_xboole_0(X2)) )),
% 0.20/0.50    inference(resolution,[],[f49,f33])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.20/0.50    inference(flattening,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_funct_2)).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ~r1_tarski(k3_tarski(sK3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))))),
% 0.20/0.50    inference(backward_demodulation,[],[f37,f54])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ~r1_tarski(k5_setfam_1(sK0,sK3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))))),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (27058)------------------------------
% 0.20/0.50  % (27058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (27058)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (27058)Memory used [KB]: 1791
% 0.20/0.50  % (27058)Time elapsed: 0.096 s
% 0.20/0.50  % (27058)------------------------------
% 0.20/0.50  % (27058)------------------------------
% 0.20/0.51  % (27048)Success in time 0.148 s
%------------------------------------------------------------------------------
