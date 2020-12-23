%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 940 expanded)
%              Number of leaves         :   19 ( 362 expanded)
%              Depth                    :   20
%              Number of atoms          :  472 (6300 expanded)
%              Number of equality atoms :   97 (1087 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f487,plain,(
    $false ),
    inference(subsumption_resolution,[],[f486,f51])).

fof(f51,plain,(
    ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ v4_pre_topc(sK3,sK2)
    & sK1 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v4_pre_topc(sK1,sK0)
    & m1_pre_topc(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f30,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v4_pre_topc(X3,X2)
                    & X1 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
                & v4_pre_topc(X1,X0)
                & m1_pre_topc(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,sK0)
              & m1_pre_topc(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v4_pre_topc(X3,X2)
                & X1 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
            & v4_pre_topc(X1,sK0)
            & m1_pre_topc(X2,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v4_pre_topc(X3,X2)
              & sK1 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
          & v4_pre_topc(sK1,sK0)
          & m1_pre_topc(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v4_pre_topc(X3,X2)
            & sK1 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
        & v4_pre_topc(sK1,sK0)
        & m1_pre_topc(X2,sK0) )
   => ( ? [X3] :
          ( ~ v4_pre_topc(X3,sK2)
          & sK1 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
      & v4_pre_topc(sK1,sK0)
      & m1_pre_topc(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X3] :
        ( ~ v4_pre_topc(X3,sK2)
        & sK1 = X3
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ~ v4_pre_topc(sK3,sK2)
      & sK1 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v4_pre_topc(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X1 = X3
                       => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v4_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_2)).

fof(f486,plain,(
    v4_pre_topc(sK3,sK2) ),
    inference(forward_demodulation,[],[f485,f189])).

fof(f189,plain,(
    sK3 = k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3)) ),
    inference(forward_demodulation,[],[f187,f170])).

fof(f170,plain,(
    sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))) ),
    inference(backward_demodulation,[],[f137,f167])).

fof(f167,plain,(
    sK3 = k2_struct_0(k1_pre_topc(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f164,f93])).

fof(f93,plain,(
    l1_pre_topc(sK2) ),
    inference(resolution,[],[f92,f47])).

fof(f47,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f92,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f63,f45])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f164,plain,
    ( sK3 = k2_struct_0(k1_pre_topc(sK2,sK3))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f86,f49])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f31])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f85,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_pre_topc(k1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f85,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f83,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_pre_topc(X0,X1) = X2
                  | k2_struct_0(X2) != X1 )
                & ( k2_struct_0(X2) = X1
                  | k1_pre_topc(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).

fof(f137,plain,(
    k2_struct_0(k1_pre_topc(sK2,sK3)) = k1_setfam_1(k2_tarski(k2_struct_0(k1_pre_topc(sK2,sK3)),k2_struct_0(sK2))) ),
    inference(resolution,[],[f135,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f54,f66])).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f135,plain,(
    r1_tarski(k2_struct_0(k1_pre_topc(sK2,sK3)),k2_struct_0(sK2)) ),
    inference(resolution,[],[f124,f49])).

fof(f124,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_tarski(k2_struct_0(k1_pre_topc(sK2,X1)),k2_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f123,f93])).

fof(f123,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_tarski(k2_struct_0(k1_pre_topc(sK2,X1)),k2_struct_0(sK2))
      | ~ l1_pre_topc(sK2) ) ),
    inference(resolution,[],[f112,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f67,f63])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ( ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK5(X0,X1)
                      | ~ r2_hidden(X3,u1_pre_topc(X0))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(sK5(X0,X1),u1_pre_topc(X1)) )
                & ( ( sK5(X0,X1) = k9_subset_1(u1_struct_0(X1),sK6(X0,X1),k2_struct_0(X1))
                    & r2_hidden(sK6(X0,X1),u1_pre_topc(X0))
                    & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
                  | r2_hidden(sK5(X0,X1),u1_pre_topc(X1)) )
                & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X5] :
                    ( ( ( r2_hidden(X5,u1_pre_topc(X1))
                        | ! [X6] :
                            ( k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5
                            | ~ r2_hidden(X6,u1_pre_topc(X0))
                            | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ( k9_subset_1(u1_struct_0(X1),sK7(X0,X1,X5),k2_struct_0(X1)) = X5
                          & r2_hidden(sK7(X0,X1,X5),u1_pre_topc(X0))
                          & m1_subset_1(sK7(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X5,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f40,f43,f42,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                | ~ r2_hidden(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X2,u1_pre_topc(X1)) )
          & ( ? [X4] :
                ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                & r2_hidden(X4,u1_pre_topc(X0))
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X2,u1_pre_topc(X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK5(X0,X1)
              | ~ r2_hidden(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r2_hidden(sK5(X0,X1),u1_pre_topc(X1)) )
        & ( ? [X4] :
              ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK5(X0,X1)
              & r2_hidden(X4,u1_pre_topc(X0))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | r2_hidden(sK5(X0,X1),u1_pre_topc(X1)) )
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK5(X0,X1)
          & r2_hidden(X4,u1_pre_topc(X0))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK5(X0,X1) = k9_subset_1(u1_struct_0(X1),sK6(X0,X1),k2_struct_0(X1))
        & r2_hidden(sK6(X0,X1),u1_pre_topc(X0))
        & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5
          & r2_hidden(X7,u1_pre_topc(X0))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK7(X0,X1,X5),k2_struct_0(X1)) = X5
        & r2_hidden(sK7(X0,X1,X5),u1_pre_topc(X0))
        & m1_subset_1(sK7(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ( ! [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                        | ~ r2_hidden(X3,u1_pre_topc(X0))
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X2,u1_pre_topc(X1)) )
                  & ( ? [X4] :
                        ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                        & r2_hidden(X4,u1_pre_topc(X0))
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    | r2_hidden(X2,u1_pre_topc(X1)) )
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X5] :
                    ( ( ( r2_hidden(X5,u1_pre_topc(X1))
                        | ! [X6] :
                            ( k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5
                            | ~ r2_hidden(X6,u1_pre_topc(X0))
                            | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ? [X7] :
                            ( k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5
                            & r2_hidden(X7,u1_pre_topc(X0))
                            & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X5,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ( ! [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                        | ~ r2_hidden(X3,u1_pre_topc(X0))
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X2,u1_pre_topc(X1)) )
                  & ( ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | r2_hidden(X2,u1_pre_topc(X1)) )
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X2] :
                    ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                        | ! [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                            | ~ r2_hidden(X3,u1_pre_topc(X0))
                            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ? [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                            & r2_hidden(X3,u1_pre_topc(X0))
                            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ( ! [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                        | ~ r2_hidden(X3,u1_pre_topc(X0))
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X2,u1_pre_topc(X1)) )
                  & ( ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | r2_hidden(X2,u1_pre_topc(X1)) )
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X2] :
                    ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                        | ! [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                            | ~ r2_hidden(X3,u1_pre_topc(X0))
                            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ? [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                            & r2_hidden(X3,u1_pre_topc(X0))
                            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

fof(f112,plain,(
    ! [X1] :
      ( m1_pre_topc(k1_pre_topc(sK2,X1),sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f60,f93])).

fof(f187,plain,(
    k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))) = k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3)) ),
    inference(superposition,[],[f173,f156])).

fof(f156,plain,(
    ! [X2] : k9_subset_1(k2_struct_0(sK0),X2,k2_struct_0(sK2)) = k1_setfam_1(k2_tarski(X2,k2_struct_0(sK2))) ),
    inference(resolution,[],[f151,f101])).

fof(f101,plain,(
    r1_tarski(k2_struct_0(sK2),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f100,f45])).

fof(f100,plain,
    ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f91,f47])).

fof(f151,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,X2)
      | k9_subset_1(X2,X3,X4) = k1_setfam_1(k2_tarski(X3,X4)) ) ),
    inference(resolution,[],[f79,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f53,f66])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f173,plain,(
    ! [X3] : k9_subset_1(k2_struct_0(sK0),sK3,X3) = k1_setfam_1(k2_tarski(X3,sK3)) ),
    inference(backward_demodulation,[],[f162,f172])).

fof(f172,plain,(
    sK3 = k2_struct_0(k1_pre_topc(sK0,sK3)) ),
    inference(subsumption_resolution,[],[f165,f45])).

fof(f165,plain,
    ( sK3 = k2_struct_0(k1_pre_topc(sK0,sK3))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f86,f78])).

fof(f78,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(definition_unfolding,[],[f46,f50])).

fof(f50,plain,(
    sK1 = sK3 ),
    inference(cnf_transformation,[],[f31])).

fof(f46,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f162,plain,(
    ! [X3] : k9_subset_1(k2_struct_0(sK0),k2_struct_0(k1_pre_topc(sK0,sK3)),X3) = k1_setfam_1(k2_tarski(X3,k2_struct_0(k1_pre_topc(sK0,sK3)))) ),
    inference(backward_demodulation,[],[f145,f157])).

fof(f157,plain,(
    ! [X3] : k9_subset_1(k2_struct_0(sK0),X3,k2_struct_0(k1_pre_topc(sK0,sK3))) = k1_setfam_1(k2_tarski(X3,k2_struct_0(k1_pre_topc(sK0,sK3)))) ),
    inference(resolution,[],[f151,f131])).

fof(f131,plain,(
    r1_tarski(k2_struct_0(k1_pre_topc(sK0,sK3)),k2_struct_0(sK0)) ),
    inference(resolution,[],[f115,f78])).

fof(f115,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k2_struct_0(k1_pre_topc(sK0,X1)),k2_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f114,f45])).

fof(f114,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k2_struct_0(k1_pre_topc(sK0,X1)),k2_struct_0(sK0))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f111,f91])).

fof(f111,plain,(
    ! [X0] :
      ( m1_pre_topc(k1_pre_topc(sK0,X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f60,f45])).

fof(f145,plain,(
    ! [X3] : k9_subset_1(k2_struct_0(sK0),X3,k2_struct_0(k1_pre_topc(sK0,sK3))) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(k1_pre_topc(sK0,sK3)),X3) ),
    inference(resolution,[],[f141,f131])).

fof(f141,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,X2)
      | k9_subset_1(X2,X3,X4) = k9_subset_1(X2,X4,X3) ) ),
    inference(resolution,[],[f52,f65])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f485,plain,(
    v4_pre_topc(k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3)),sK2) ),
    inference(forward_demodulation,[],[f484,f152])).

fof(f152,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK2),sK3,X0) = k1_setfam_1(k2_tarski(X0,sK3)) ),
    inference(backward_demodulation,[],[f139,f149])).

fof(f149,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK2),X0,sK3) = k1_setfam_1(k2_tarski(X0,sK3)) ),
    inference(resolution,[],[f79,f49])).

fof(f139,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK2),X0,sK3) = k9_subset_1(u1_struct_0(sK2),sK3,X0) ),
    inference(resolution,[],[f52,f49])).

fof(f484,plain,(
    v4_pre_topc(k9_subset_1(u1_struct_0(sK2),sK3,k2_struct_0(sK2)),sK2) ),
    inference(subsumption_resolution,[],[f483,f49])).

fof(f483,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),sK3,k2_struct_0(sK2)),sK2) ),
    inference(forward_demodulation,[],[f482,f189])).

fof(f482,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),sK3,k2_struct_0(sK2)),sK2) ),
    inference(forward_demodulation,[],[f479,f152])).

fof(f479,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),sK3,k2_struct_0(sK2)),sK2) ),
    inference(resolution,[],[f477,f47])).

fof(f477,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),sK3,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k9_subset_1(u1_struct_0(X0),sK3,k2_struct_0(X0)),X0) ) ),
    inference(subsumption_resolution,[],[f476,f45])).

fof(f476,plain,(
    ! [X0] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(X0),sK3,k2_struct_0(X0)),X0)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),sK3,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f473,f78])).

fof(f473,plain,(
    ! [X0] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(X0),sK3,k2_struct_0(X0)),X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),sK3,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f81,f77])).

fof(f77,plain,(
    v4_pre_topc(sK3,sK0) ),
    inference(definition_unfolding,[],[f48,f50])).

fof(f48,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( ~ v4_pre_topc(X3,X0)
      | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(X2,X1)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2
                    & v4_pre_topc(sK4(X0,X1,X2),X0)
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
          & v4_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2
        & v4_pre_topc(sK4(X0,X1,X2),X0)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                      & v4_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_pre_topc)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:13:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (11987)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.50  % (11998)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (11979)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.50  % (11990)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.50  % (11980)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (11976)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (11981)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (11982)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (12002)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.51  % (11998)Refutation not found, incomplete strategy% (11998)------------------------------
% 0.20/0.51  % (11998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (11998)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (11998)Memory used [KB]: 10874
% 0.20/0.51  % (11998)Time elapsed: 0.060 s
% 0.20/0.51  % (11998)------------------------------
% 0.20/0.51  % (11998)------------------------------
% 0.20/0.51  % (12004)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.51  % (11978)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (11977)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (11978)Refutation not found, incomplete strategy% (11978)------------------------------
% 0.20/0.52  % (11978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (11989)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (11995)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.52  % (11996)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (12003)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.52  % (11994)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (11993)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (11988)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (11991)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (11997)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (11986)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (11984)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (11993)Refutation not found, incomplete strategy% (11993)------------------------------
% 0.20/0.53  % (11993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (11993)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (11993)Memory used [KB]: 10618
% 0.20/0.53  % (11993)Time elapsed: 0.131 s
% 0.20/0.53  % (11993)------------------------------
% 0.20/0.53  % (11993)------------------------------
% 0.20/0.53  % (12000)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (11985)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (12001)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (11980)Refutation not found, incomplete strategy% (11980)------------------------------
% 0.20/0.53  % (11980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (11980)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (11980)Memory used [KB]: 6652
% 0.20/0.53  % (11980)Time elapsed: 0.135 s
% 0.20/0.53  % (11980)------------------------------
% 0.20/0.53  % (11980)------------------------------
% 0.20/0.54  % (11999)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (11978)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (11978)Memory used [KB]: 10874
% 0.20/0.54  % (11978)Time elapsed: 0.109 s
% 0.20/0.54  % (11978)------------------------------
% 0.20/0.54  % (11978)------------------------------
% 0.20/0.54  % (12005)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (11986)Refutation not found, incomplete strategy% (11986)------------------------------
% 0.20/0.54  % (11986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (11986)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (11986)Memory used [KB]: 10746
% 0.20/0.54  % (11986)Time elapsed: 0.135 s
% 0.20/0.54  % (11986)------------------------------
% 0.20/0.54  % (11986)------------------------------
% 0.20/0.54  % (11983)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (11992)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (11981)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % (11984)Refutation not found, incomplete strategy% (11984)------------------------------
% 0.20/0.55  % (11984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (11984)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (11984)Memory used [KB]: 11001
% 0.20/0.55  % (11984)Time elapsed: 0.155 s
% 0.20/0.55  % (11984)------------------------------
% 0.20/0.55  % (11984)------------------------------
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f487,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(subsumption_resolution,[],[f486,f51])).
% 0.20/0.57  fof(f51,plain,(
% 0.20/0.57    ~v4_pre_topc(sK3,sK2)),
% 0.20/0.57    inference(cnf_transformation,[],[f31])).
% 0.20/0.57  fof(f31,plain,(
% 0.20/0.57    (((~v4_pre_topc(sK3,sK2) & sK1 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & v4_pre_topc(sK1,sK0) & m1_pre_topc(sK2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f30,f29,f28,f27])).
% 0.20/0.57  fof(f27,plain,(
% 0.20/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,sK0) & m1_pre_topc(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f28,plain,(
% 0.20/0.57    ? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,sK0) & m1_pre_topc(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(sK1,sK0) & m1_pre_topc(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    ? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(sK1,sK0) & m1_pre_topc(X2,sK0)) => (? [X3] : (~v4_pre_topc(X3,sK2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & v4_pre_topc(sK1,sK0) & m1_pre_topc(sK2,sK0))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f30,plain,(
% 0.20/0.57    ? [X3] : (~v4_pre_topc(X3,sK2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) => (~v4_pre_topc(sK3,sK2) & sK1 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f16,plain,(
% 0.20/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.57    inference(flattening,[],[f15])).
% 0.20/0.57  fof(f15,plain,(
% 0.20/0.57    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v4_pre_topc(X3,X2) & X1 = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0)) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f14])).
% 0.20/0.57  fof(f14,negated_conjecture,(
% 0.20/0.57    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 0.20/0.57    inference(negated_conjecture,[],[f13])).
% 0.20/0.57  fof(f13,conjecture,(
% 0.20/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_2)).
% 0.20/0.57  fof(f486,plain,(
% 0.20/0.57    v4_pre_topc(sK3,sK2)),
% 0.20/0.57    inference(forward_demodulation,[],[f485,f189])).
% 0.20/0.57  fof(f189,plain,(
% 0.20/0.57    sK3 = k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3))),
% 0.20/0.57    inference(forward_demodulation,[],[f187,f170])).
% 0.20/0.57  fof(f170,plain,(
% 0.20/0.57    sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2)))),
% 0.20/0.57    inference(backward_demodulation,[],[f137,f167])).
% 0.20/0.57  fof(f167,plain,(
% 0.20/0.57    sK3 = k2_struct_0(k1_pre_topc(sK2,sK3))),
% 0.20/0.57    inference(subsumption_resolution,[],[f164,f93])).
% 0.20/0.57  fof(f93,plain,(
% 0.20/0.57    l1_pre_topc(sK2)),
% 0.20/0.57    inference(resolution,[],[f92,f47])).
% 0.20/0.57  fof(f47,plain,(
% 0.20/0.57    m1_pre_topc(sK2,sK0)),
% 0.20/0.57    inference(cnf_transformation,[],[f31])).
% 0.20/0.57  fof(f92,plain,(
% 0.20/0.57    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 0.20/0.57    inference(resolution,[],[f63,f45])).
% 0.20/0.57  fof(f45,plain,(
% 0.20/0.57    l1_pre_topc(sK0)),
% 0.20/0.57    inference(cnf_transformation,[],[f31])).
% 0.20/0.57  fof(f63,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f25])).
% 0.20/0.57  fof(f25,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f11])).
% 0.20/0.57  fof(f11,axiom,(
% 0.20/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.57  fof(f164,plain,(
% 0.20/0.57    sK3 = k2_struct_0(k1_pre_topc(sK2,sK3)) | ~l1_pre_topc(sK2)),
% 0.20/0.57    inference(resolution,[],[f86,f49])).
% 0.20/0.57  fof(f49,plain,(
% 0.20/0.57    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.57    inference(cnf_transformation,[],[f31])).
% 0.20/0.57  fof(f86,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~l1_pre_topc(X0)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f85,f59])).
% 0.20/0.57  fof(f59,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_pre_topc(k1_pre_topc(X0,X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f22])).
% 0.20/0.57  fof(f22,plain,(
% 0.20/0.57    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.57    inference(flattening,[],[f21])).
% 0.20/0.57  fof(f21,plain,(
% 0.20/0.57    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f10])).
% 0.20/0.57  fof(f10,axiom,(
% 0.20/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.20/0.57  fof(f85,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f83,f60])).
% 0.20/0.57  fof(f60,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(k1_pre_topc(X0,X1),X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f22])).
% 0.20/0.57  fof(f83,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.57    inference(equality_resolution,[],[f61])).
% 0.20/0.57  fof(f61,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f36])).
% 0.20/0.57  fof(f36,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (! [X2] : (((k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1) & (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.57    inference(nnf_transformation,[],[f24])).
% 0.20/0.57  fof(f24,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.57    inference(flattening,[],[f23])).
% 0.20/0.57  fof(f23,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f8])).
% 0.20/0.57  fof(f8,axiom,(
% 0.20/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).
% 0.20/0.57  fof(f137,plain,(
% 0.20/0.57    k2_struct_0(k1_pre_topc(sK2,sK3)) = k1_setfam_1(k2_tarski(k2_struct_0(k1_pre_topc(sK2,sK3)),k2_struct_0(sK2)))),
% 0.20/0.57    inference(resolution,[],[f135,f80])).
% 0.20/0.57  fof(f80,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 0.20/0.57    inference(definition_unfolding,[],[f54,f66])).
% 0.20/0.57  fof(f66,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,axiom,(
% 0.20/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.57  fof(f54,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f19,plain,(
% 0.20/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f1])).
% 0.20/0.57  fof(f1,axiom,(
% 0.20/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.57  fof(f135,plain,(
% 0.20/0.57    r1_tarski(k2_struct_0(k1_pre_topc(sK2,sK3)),k2_struct_0(sK2))),
% 0.20/0.57    inference(resolution,[],[f124,f49])).
% 0.20/0.57  fof(f124,plain,(
% 0.20/0.57    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | r1_tarski(k2_struct_0(k1_pre_topc(sK2,X1)),k2_struct_0(sK2))) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f123,f93])).
% 0.20/0.57  fof(f123,plain,(
% 0.20/0.57    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | r1_tarski(k2_struct_0(k1_pre_topc(sK2,X1)),k2_struct_0(sK2)) | ~l1_pre_topc(sK2)) )),
% 0.20/0.57    inference(resolution,[],[f112,f91])).
% 0.20/0.57  fof(f91,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f67,f63])).
% 0.20/0.57  fof(f67,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f44])).
% 0.20/0.57  fof(f44,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (((m1_pre_topc(X1,X0) | ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK5(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK5(X0,X1),u1_pre_topc(X1))) & ((sK5(X0,X1) = k9_subset_1(u1_struct_0(X1),sK6(X0,X1),k2_struct_0(X1)) & r2_hidden(sK6(X0,X1),u1_pre_topc(X0)) & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK5(X0,X1),u1_pre_topc(X1))) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X1)) | ! [X6] : (k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5 | ~r2_hidden(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))))) & ((k9_subset_1(u1_struct_0(X1),sK7(X0,X1,X5),k2_struct_0(X1)) = X5 & r2_hidden(sK7(X0,X1,X5),u1_pre_topc(X0)) & m1_subset_1(sK7(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X5,u1_pre_topc(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~m1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f40,f43,f42,f41])).
% 0.20/0.57  fof(f41,plain,(
% 0.20/0.57    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & r2_hidden(X4,u1_pre_topc(X0)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK5(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK5(X0,X1),u1_pre_topc(X1))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK5(X0,X1) & r2_hidden(X4,u1_pre_topc(X0)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK5(X0,X1),u1_pre_topc(X1))) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f42,plain,(
% 0.20/0.57    ! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK5(X0,X1) & r2_hidden(X4,u1_pre_topc(X0)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (sK5(X0,X1) = k9_subset_1(u1_struct_0(X1),sK6(X0,X1),k2_struct_0(X1)) & r2_hidden(sK6(X0,X1),u1_pre_topc(X0)) & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f43,plain,(
% 0.20/0.57    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5 & r2_hidden(X7,u1_pre_topc(X0)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X1),sK7(X0,X1,X5),k2_struct_0(X1)) = X5 & r2_hidden(sK7(X0,X1,X5),u1_pre_topc(X0)) & m1_subset_1(sK7(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f40,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (((m1_pre_topc(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & r2_hidden(X4,u1_pre_topc(X0)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X1)) | ! [X6] : (k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5 | ~r2_hidden(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X7] : (k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5 & r2_hidden(X7,u1_pre_topc(X0)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X5,u1_pre_topc(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~m1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.57    inference(rectify,[],[f39])).
% 0.20/0.57  fof(f39,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (((m1_pre_topc(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~m1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.57    inference(flattening,[],[f38])).
% 0.20/0.57  fof(f38,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (((m1_pre_topc(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~m1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.57    inference(nnf_transformation,[],[f26])).
% 0.20/0.57  fof(f26,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f9])).
% 0.20/0.57  fof(f9,axiom,(
% 0.20/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).
% 0.20/0.57  fof(f112,plain,(
% 0.20/0.57    ( ! [X1] : (m1_pre_topc(k1_pre_topc(sK2,X1),sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.20/0.57    inference(resolution,[],[f60,f93])).
% 0.20/0.57  fof(f187,plain,(
% 0.20/0.57    k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))) = k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3))),
% 0.20/0.57    inference(superposition,[],[f173,f156])).
% 0.20/0.57  fof(f156,plain,(
% 0.20/0.57    ( ! [X2] : (k9_subset_1(k2_struct_0(sK0),X2,k2_struct_0(sK2)) = k1_setfam_1(k2_tarski(X2,k2_struct_0(sK2)))) )),
% 0.20/0.57    inference(resolution,[],[f151,f101])).
% 0.20/0.57  fof(f101,plain,(
% 0.20/0.57    r1_tarski(k2_struct_0(sK2),k2_struct_0(sK0))),
% 0.20/0.57    inference(subsumption_resolution,[],[f100,f45])).
% 0.20/0.57  fof(f100,plain,(
% 0.20/0.57    r1_tarski(k2_struct_0(sK2),k2_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 0.20/0.57    inference(resolution,[],[f91,f47])).
% 0.20/0.57  fof(f151,plain,(
% 0.20/0.57    ( ! [X4,X2,X3] : (~r1_tarski(X4,X2) | k9_subset_1(X2,X3,X4) = k1_setfam_1(k2_tarski(X3,X4))) )),
% 0.20/0.57    inference(resolution,[],[f79,f65])).
% 0.20/0.57  fof(f65,plain,(
% 0.20/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f37])).
% 0.20/0.57  fof(f37,plain,(
% 0.20/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.57    inference(nnf_transformation,[],[f7])).
% 0.20/0.57  fof(f7,axiom,(
% 0.20/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.57  fof(f79,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 0.20/0.57    inference(definition_unfolding,[],[f53,f66])).
% 0.20/0.57  fof(f53,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f18])).
% 0.20/0.57  fof(f18,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f5])).
% 0.20/0.57  fof(f5,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.57  fof(f173,plain,(
% 0.20/0.57    ( ! [X3] : (k9_subset_1(k2_struct_0(sK0),sK3,X3) = k1_setfam_1(k2_tarski(X3,sK3))) )),
% 0.20/0.57    inference(backward_demodulation,[],[f162,f172])).
% 0.20/0.57  fof(f172,plain,(
% 0.20/0.57    sK3 = k2_struct_0(k1_pre_topc(sK0,sK3))),
% 0.20/0.57    inference(subsumption_resolution,[],[f165,f45])).
% 0.20/0.57  fof(f165,plain,(
% 0.20/0.57    sK3 = k2_struct_0(k1_pre_topc(sK0,sK3)) | ~l1_pre_topc(sK0)),
% 0.20/0.57    inference(resolution,[],[f86,f78])).
% 0.20/0.57  fof(f78,plain,(
% 0.20/0.57    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.57    inference(definition_unfolding,[],[f46,f50])).
% 0.20/0.57  fof(f50,plain,(
% 0.20/0.57    sK1 = sK3),
% 0.20/0.57    inference(cnf_transformation,[],[f31])).
% 0.20/0.57  fof(f46,plain,(
% 0.20/0.57    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.57    inference(cnf_transformation,[],[f31])).
% 0.20/0.57  fof(f162,plain,(
% 0.20/0.57    ( ! [X3] : (k9_subset_1(k2_struct_0(sK0),k2_struct_0(k1_pre_topc(sK0,sK3)),X3) = k1_setfam_1(k2_tarski(X3,k2_struct_0(k1_pre_topc(sK0,sK3))))) )),
% 0.20/0.57    inference(backward_demodulation,[],[f145,f157])).
% 0.20/0.57  fof(f157,plain,(
% 0.20/0.57    ( ! [X3] : (k9_subset_1(k2_struct_0(sK0),X3,k2_struct_0(k1_pre_topc(sK0,sK3))) = k1_setfam_1(k2_tarski(X3,k2_struct_0(k1_pre_topc(sK0,sK3))))) )),
% 0.20/0.57    inference(resolution,[],[f151,f131])).
% 0.20/0.57  fof(f131,plain,(
% 0.20/0.57    r1_tarski(k2_struct_0(k1_pre_topc(sK0,sK3)),k2_struct_0(sK0))),
% 0.20/0.57    inference(resolution,[],[f115,f78])).
% 0.20/0.57  fof(f115,plain,(
% 0.20/0.57    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_struct_0(k1_pre_topc(sK0,X1)),k2_struct_0(sK0))) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f114,f45])).
% 0.20/0.57  fof(f114,plain,(
% 0.20/0.57    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_struct_0(k1_pre_topc(sK0,X1)),k2_struct_0(sK0)) | ~l1_pre_topc(sK0)) )),
% 0.20/0.57    inference(resolution,[],[f111,f91])).
% 0.20/0.57  fof(f111,plain,(
% 0.20/0.57    ( ! [X0] : (m1_pre_topc(k1_pre_topc(sK0,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.57    inference(resolution,[],[f60,f45])).
% 0.20/0.57  fof(f145,plain,(
% 0.20/0.57    ( ! [X3] : (k9_subset_1(k2_struct_0(sK0),X3,k2_struct_0(k1_pre_topc(sK0,sK3))) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(k1_pre_topc(sK0,sK3)),X3)) )),
% 0.20/0.57    inference(resolution,[],[f141,f131])).
% 0.20/0.57  fof(f141,plain,(
% 0.20/0.57    ( ! [X4,X2,X3] : (~r1_tarski(X4,X2) | k9_subset_1(X2,X3,X4) = k9_subset_1(X2,X4,X3)) )),
% 0.20/0.57    inference(resolution,[],[f52,f65])).
% 0.20/0.57  fof(f52,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f17])).
% 0.20/0.57  fof(f17,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f2])).
% 0.20/0.57  fof(f2,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 0.20/0.57  fof(f485,plain,(
% 0.20/0.57    v4_pre_topc(k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3)),sK2)),
% 0.20/0.57    inference(forward_demodulation,[],[f484,f152])).
% 0.20/0.57  fof(f152,plain,(
% 0.20/0.57    ( ! [X0] : (k9_subset_1(u1_struct_0(sK2),sK3,X0) = k1_setfam_1(k2_tarski(X0,sK3))) )),
% 0.20/0.57    inference(backward_demodulation,[],[f139,f149])).
% 0.20/0.57  fof(f149,plain,(
% 0.20/0.57    ( ! [X0] : (k9_subset_1(u1_struct_0(sK2),X0,sK3) = k1_setfam_1(k2_tarski(X0,sK3))) )),
% 0.20/0.57    inference(resolution,[],[f79,f49])).
% 0.20/0.57  fof(f139,plain,(
% 0.20/0.57    ( ! [X0] : (k9_subset_1(u1_struct_0(sK2),X0,sK3) = k9_subset_1(u1_struct_0(sK2),sK3,X0)) )),
% 0.20/0.57    inference(resolution,[],[f52,f49])).
% 0.20/0.57  fof(f484,plain,(
% 0.20/0.57    v4_pre_topc(k9_subset_1(u1_struct_0(sK2),sK3,k2_struct_0(sK2)),sK2)),
% 0.20/0.57    inference(subsumption_resolution,[],[f483,f49])).
% 0.20/0.57  fof(f483,plain,(
% 0.20/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),sK3,k2_struct_0(sK2)),sK2)),
% 0.20/0.57    inference(forward_demodulation,[],[f482,f189])).
% 0.20/0.57  fof(f482,plain,(
% 0.20/0.57    ~m1_subset_1(k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3)),k1_zfmisc_1(u1_struct_0(sK2))) | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),sK3,k2_struct_0(sK2)),sK2)),
% 0.20/0.57    inference(forward_demodulation,[],[f479,f152])).
% 0.20/0.57  fof(f479,plain,(
% 0.20/0.57    ~m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),sK3,k2_struct_0(sK2)),sK2)),
% 0.20/0.57    inference(resolution,[],[f477,f47])).
% 0.20/0.58  fof(f477,plain,(
% 0.20/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_subset_1(k9_subset_1(u1_struct_0(X0),sK3,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k9_subset_1(u1_struct_0(X0),sK3,k2_struct_0(X0)),X0)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f476,f45])).
% 0.20/0.58  fof(f476,plain,(
% 0.20/0.58    ( ! [X0] : (v4_pre_topc(k9_subset_1(u1_struct_0(X0),sK3,k2_struct_0(X0)),X0) | ~m1_subset_1(k9_subset_1(u1_struct_0(X0),sK3,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f473,f78])).
% 0.20/0.58  fof(f473,plain,(
% 0.20/0.58    ( ! [X0] : (v4_pre_topc(k9_subset_1(u1_struct_0(X0),sK3,k2_struct_0(X0)),X0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X0),sK3,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) )),
% 0.20/0.58    inference(resolution,[],[f81,f77])).
% 0.20/0.58  fof(f77,plain,(
% 0.20/0.58    v4_pre_topc(sK3,sK0)),
% 0.20/0.58    inference(definition_unfolding,[],[f48,f50])).
% 0.20/0.58  fof(f48,plain,(
% 0.20/0.58    v4_pre_topc(sK1,sK0)),
% 0.20/0.58    inference(cnf_transformation,[],[f31])).
% 0.20/0.58  fof(f81,plain,(
% 0.20/0.58    ( ! [X0,X3,X1] : (~v4_pre_topc(X3,X0) | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.58    inference(equality_resolution,[],[f58])).
% 0.20/0.58  fof(f58,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (v4_pre_topc(X2,X1) | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f35])).
% 0.20/0.58  fof(f35,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (! [X2] : (((v4_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2 & v4_pre_topc(sK4(X0,X1,X2),X0) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).
% 0.20/0.58  fof(f34,plain,(
% 0.20/0.58    ! [X2,X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v4_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2 & v4_pre_topc(sK4(X0,X1,X2),X0) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f33,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (! [X2] : (((v4_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v4_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.58    inference(rectify,[],[f32])).
% 0.20/0.58  fof(f32,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (! [X2] : (((v4_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.58    inference(nnf_transformation,[],[f20])).
% 0.20/0.58  fof(f20,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f12])).
% 0.20/0.58  fof(f12,axiom,(
% 0.20/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_pre_topc)).
% 0.20/0.58  % SZS output end Proof for theBenchmark
% 0.20/0.58  % (11981)------------------------------
% 0.20/0.58  % (11981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (11981)Termination reason: Refutation
% 0.20/0.58  
% 0.20/0.58  % (11981)Memory used [KB]: 6908
% 0.20/0.58  % (11981)Time elapsed: 0.159 s
% 0.20/0.58  % (11981)------------------------------
% 0.20/0.58  % (11981)------------------------------
% 0.20/0.58  % (11975)Success in time 0.227 s
%------------------------------------------------------------------------------
