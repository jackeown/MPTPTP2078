%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 160 expanded)
%              Number of leaves         :   16 (  55 expanded)
%              Depth                    :   20
%              Number of atoms          :  277 ( 518 expanded)
%              Number of equality atoms :  114 ( 160 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f144,plain,(
    $false ),
    inference(subsumption_resolution,[],[f139,f33])).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)))
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

fof(f139,plain,(
    ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f138,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f86,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

% (27668)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f86,plain,(
    ! [X0,X1] : m1_subset_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f62,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f40,f59])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f54,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f55,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f138,plain,(
    ~ v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f137,f33])).

fof(f137,plain,
    ( ~ v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f136,f32])).

fof(f32,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f136,plain,
    ( ~ v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f135,f62])).

fof(f135,plain,
    ( ~ v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)))
    | ~ r1_tarski(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)),sK1)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1) ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,
    ( ~ v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)))
    | ~ r1_tarski(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)),sK1)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))) ),
    inference(resolution,[],[f133,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

fof(f133,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f132,f34])).

fof(f34,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f132,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f131,f32])).

fof(f131,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f130,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] : r1_tarski(k1_setfam_1(k3_enumset1(X0,X0,X1,X2,X3)),X3) ),
    inference(resolution,[],[f74,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_setfam_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f74,plain,(
    ! [X6,X2,X0,X1] : r2_hidden(X6,k3_enumset1(X0,X0,X1,X2,X6)) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X1] :
      ( r2_hidden(X6,X4)
      | k3_enumset1(X0,X0,X1,X2,X6) != X4 ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r2_hidden(X6,X4)
      | X3 != X6
      | k3_enumset1(X0,X0,X1,X2,X3) != X4 ) ),
    inference(definition_unfolding,[],[f48,f56])).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r2_hidden(X6,X4)
      | X3 != X6
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ( ( ( sK3(X0,X1,X2,X3,X4) != X3
              & sK3(X0,X1,X2,X3,X4) != X2
              & sK3(X0,X1,X2,X3,X4) != X1
              & sK3(X0,X1,X2,X3,X4) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3,X4),X4) )
          & ( sK3(X0,X1,X2,X3,X4) = X3
            | sK3(X0,X1,X2,X3,X4) = X2
            | sK3(X0,X1,X2,X3,X4) = X1
            | sK3(X0,X1,X2,X3,X4) = X0
            | r2_hidden(sK3(X0,X1,X2,X3,X4),X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

% (27688)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f30,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 )
            | ~ r2_hidden(X5,X4) )
          & ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5
            | r2_hidden(X5,X4) ) )
     => ( ( ( sK3(X0,X1,X2,X3,X4) != X3
            & sK3(X0,X1,X2,X3,X4) != X2
            & sK3(X0,X1,X2,X3,X4) != X1
            & sK3(X0,X1,X2,X3,X4) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3,X4),X4) )
        & ( sK3(X0,X1,X2,X3,X4) = X3
          | sK3(X0,X1,X2,X3,X4) = X2
          | sK3(X0,X1,X2,X3,X4) = X1
          | sK3(X0,X1,X2,X3,X4) = X0
          | r2_hidden(sK3(X0,X1,X2,X3,X4),X4) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

% (27680)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

fof(f130,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1))
    | ~ r1_tarski(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)),sK2)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))) ),
    inference(resolution,[],[f129,f41])).

fof(f129,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2))
    | ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f60,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f59])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f60,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k1_setfam_1(k3_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))) ),
    inference(definition_unfolding,[],[f35,f59,f59])).

fof(f35,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:56:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (27665)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.51  % (27693)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.51  % (27672)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.51  % (27670)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (27669)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (27671)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % (27674)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.51  % (27672)Refutation not found, incomplete strategy% (27672)------------------------------
% 0.22/0.51  % (27672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (27672)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (27672)Memory used [KB]: 10746
% 0.22/0.51  % (27672)Time elapsed: 0.101 s
% 0.22/0.51  % (27672)------------------------------
% 0.22/0.51  % (27672)------------------------------
% 0.22/0.52  % (27675)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (27664)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (27681)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.52  % (27678)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (27681)Refutation not found, incomplete strategy% (27681)------------------------------
% 0.22/0.52  % (27681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (27681)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (27681)Memory used [KB]: 10618
% 0.22/0.52  % (27681)Time elapsed: 0.114 s
% 0.22/0.52  % (27681)------------------------------
% 0.22/0.52  % (27681)------------------------------
% 0.22/0.52  % (27679)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (27691)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.52  % (27682)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.52  % (27669)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (27683)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.52  % (27684)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % (27677)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f144,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f139,f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    v1_relat_1(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ((~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) & v1_relat_1(sK2)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f24,f23,f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) => (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) & v1_relat_1(sK2))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,negated_conjecture,(
% 0.22/0.52    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 0.22/0.52    inference(negated_conjecture,[],[f12])).
% 0.22/0.52  fof(f12,conjecture,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    ~v1_relat_1(sK1)),
% 0.22/0.52    inference(resolution,[],[f138,f91])).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(resolution,[],[f86,f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  % (27668)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    ( ! [X0,X1] : (m1_subset_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_zfmisc_1(X0))) )),
% 0.22/0.52    inference(resolution,[],[f62,f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.52    inference(nnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),X0)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f40,f59])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f42,f58])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f55,f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f54,f56])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    ~v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)))),
% 0.22/0.52    inference(subsumption_resolution,[],[f137,f33])).
% 0.22/0.52  fof(f137,plain,(
% 0.22/0.52    ~v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))) | ~v1_relat_1(sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f136,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    v1_relat_1(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f136,plain,(
% 0.22/0.52    ~v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))) | ~v1_relat_1(sK0) | ~v1_relat_1(sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f135,f62])).
% 0.22/0.52  fof(f135,plain,(
% 0.22/0.52    ~v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))) | ~r1_tarski(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)),sK1) | ~v1_relat_1(sK0) | ~v1_relat_1(sK1)),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f134])).
% 0.22/0.52  fof(f134,plain,(
% 0.22/0.52    ~v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))) | ~r1_tarski(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)),sK1) | ~v1_relat_1(sK0) | ~v1_relat_1(sK1) | ~v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)))),
% 0.22/0.52    inference(resolution,[],[f133,f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).
% 0.22/0.52  fof(f133,plain,(
% 0.22/0.52    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) | ~v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)))),
% 0.22/0.52    inference(subsumption_resolution,[],[f132,f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    v1_relat_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) | ~v1_relat_1(sK2) | ~v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)))),
% 0.22/0.52    inference(subsumption_resolution,[],[f131,f32])).
% 0.22/0.52  fof(f131,plain,(
% 0.22/0.52    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) | ~v1_relat_1(sK0) | ~v1_relat_1(sK2) | ~v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)))),
% 0.22/0.52    inference(subsumption_resolution,[],[f130,f82])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (r1_tarski(k1_setfam_1(k3_enumset1(X0,X0,X1,X2,X3)),X3)) )),
% 0.22/0.52    inference(resolution,[],[f74,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_setfam_1(X1),X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,k3_enumset1(X0,X0,X1,X2,X6))) )),
% 0.22/0.52    inference(equality_resolution,[],[f73])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    ( ! [X6,X4,X2,X0,X1] : (r2_hidden(X6,X4) | k3_enumset1(X0,X0,X1,X2,X6) != X4) )),
% 0.22/0.52    inference(equality_resolution,[],[f68])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    ( ! [X6,X4,X2,X0,X3,X1] : (r2_hidden(X6,X4) | X3 != X6 | k3_enumset1(X0,X0,X1,X2,X3) != X4) )),
% 0.22/0.52    inference(definition_unfolding,[],[f48,f56])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X6,X4,X2,X0,X3,X1] : (r2_hidden(X6,X4) | X3 != X6 | k2_enumset1(X0,X1,X2,X3) != X4) )),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | (((sK3(X0,X1,X2,X3,X4) != X3 & sK3(X0,X1,X2,X3,X4) != X2 & sK3(X0,X1,X2,X3,X4) != X1 & sK3(X0,X1,X2,X3,X4) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4),X4)) & (sK3(X0,X1,X2,X3,X4) = X3 | sK3(X0,X1,X2,X3,X4) = X2 | sK3(X0,X1,X2,X3,X4) = X1 | sK3(X0,X1,X2,X3,X4) = X0 | r2_hidden(sK3(X0,X1,X2,X3,X4),X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).
% 0.22/0.52  % (27688)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X4,X3,X2,X1,X0] : (? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4))) => (((sK3(X0,X1,X2,X3,X4) != X3 & sK3(X0,X1,X2,X3,X4) != X2 & sK3(X0,X1,X2,X3,X4) != X1 & sK3(X0,X1,X2,X3,X4) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4),X4)) & (sK3(X0,X1,X2,X3,X4) = X3 | sK3(X0,X1,X2,X3,X4) = X2 | sK3(X0,X1,X2,X3,X4) = X1 | sK3(X0,X1,X2,X3,X4) = X0 | r2_hidden(sK3(X0,X1,X2,X3,X4),X4))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 0.22/0.52    inference(rectify,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 0.22/0.52    inference(flattening,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | ~r2_hidden(X5,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 0.22/0.52    inference(nnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  % (27680)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> ~(X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).
% 0.22/0.53  fof(f130,plain,(
% 0.22/0.53    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) | ~r1_tarski(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)),sK2) | ~v1_relat_1(sK0) | ~v1_relat_1(sK2) | ~v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)))),
% 0.22/0.53    inference(resolution,[],[f129,f41])).
% 0.22/0.53  fof(f129,plain,(
% 0.22/0.53    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2)) | ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1))),
% 0.22/0.53    inference(resolution,[],[f60,f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f36,f59])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.53    inference(flattening,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k1_setfam_1(k3_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))))),
% 0.22/0.53    inference(definition_unfolding,[],[f35,f59,f59])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (27669)------------------------------
% 0.22/0.53  % (27669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (27669)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (27669)Memory used [KB]: 6268
% 0.22/0.53  % (27669)Time elapsed: 0.078 s
% 0.22/0.53  % (27669)------------------------------
% 0.22/0.53  % (27669)------------------------------
% 0.22/0.53  % (27689)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (27685)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (27663)Success in time 0.158 s
%------------------------------------------------------------------------------
