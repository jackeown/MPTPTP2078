%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:42 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 194 expanded)
%              Number of leaves         :   11 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :  171 ( 617 expanded)
%              Number of equality atoms :   24 ( 100 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f992,plain,(
    $false ),
    inference(subsumption_resolution,[],[f377,f970])).

fof(f970,plain,(
    ! [X23,X22] : r1_tarski(k1_zfmisc_1(k4_xboole_0(X22,X23)),k1_zfmisc_1(k5_xboole_0(X23,X22))) ),
    inference(superposition,[],[f374,f961])).

fof(f961,plain,(
    ! [X14,X13] : k5_xboole_0(X13,X14) = k5_xboole_0(X14,X13) ),
    inference(subsumption_resolution,[],[f959,f951])).

fof(f951,plain,(
    ! [X2,X3] : r1_tarski(k5_xboole_0(X3,X2),k5_xboole_0(X2,X3)) ),
    inference(subsumption_resolution,[],[f931,f70])).

fof(f70,plain,(
    ! [X6,X5] : r1_tarski(k4_xboole_0(X5,X6),k5_xboole_0(X5,X6)) ),
    inference(superposition,[],[f29,f31])).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

% (4415)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f931,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k4_xboole_0(X2,X3),k5_xboole_0(X2,X3))
      | r1_tarski(k5_xboole_0(X3,X2),k5_xboole_0(X2,X3)) ) ),
    inference(resolution,[],[f78,f72])).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X1,X0)) ),
    inference(resolution,[],[f69,f44])).

fof(f44,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f69,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,k4_xboole_0(X3,X2))
      | r1_tarski(X4,k5_xboole_0(X2,X3)) ) ),
    inference(superposition,[],[f42,f31])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(k4_xboole_0(X1,X0),X2)
      | r1_tarski(k5_xboole_0(X0,X1),X2) ) ),
    inference(superposition,[],[f43,f31])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f959,plain,(
    ! [X14,X13] :
      ( ~ r1_tarski(k5_xboole_0(X13,X14),k5_xboole_0(X14,X13))
      | k5_xboole_0(X13,X14) = k5_xboole_0(X14,X13) ) ),
    inference(resolution,[],[f951,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f374,plain,(
    ! [X6,X5] : r1_tarski(k1_zfmisc_1(k4_xboole_0(X5,X6)),k1_zfmisc_1(k5_xboole_0(X5,X6))) ),
    inference(superposition,[],[f363,f31])).

fof(f363,plain,(
    ! [X0,X1] : r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    inference(duplicate_literal_removal,[],[f352])).

fof(f352,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(k2_xboole_0(X0,X1)))
      | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(k2_xboole_0(X0,X1))) ) ),
    inference(resolution,[],[f114,f51])).

fof(f51,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(sK2(X1,k1_zfmisc_1(X2)),X2)
      | r1_tarski(X1,k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f37,f46])).

fof(f46,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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

fof(f114,plain,(
    ! [X21,X19,X20] :
      ( r1_tarski(sK2(k1_zfmisc_1(X19),X20),k2_xboole_0(X19,X21))
      | r1_tarski(k1_zfmisc_1(X19),X20) ) ),
    inference(resolution,[],[f106,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK2(k1_zfmisc_1(X0),X1),X0)
      | r1_tarski(k1_zfmisc_1(X0),X1) ) ),
    inference(resolution,[],[f36,f47])).

fof(f47,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f106,plain,(
    ! [X6,X7,X5] :
      ( ~ r1_tarski(X7,X5)
      | r1_tarski(X7,k2_xboole_0(X5,X6)) ) ),
    inference(superposition,[],[f42,f81])).

fof(f81,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k2_xboole_0(k2_xboole_0(X1,X2),X1) ),
    inference(resolution,[],[f79,f29])).

fof(f79,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,X4)
      | k2_xboole_0(X4,X3) = X4 ) ),
    inference(subsumption_resolution,[],[f76,f44])).

fof(f76,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,X4)
      | ~ r1_tarski(X4,X4)
      | k2_xboole_0(X4,X3) = X4 ) ),
    inference(resolution,[],[f43,f54])).

fof(f54,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_xboole_0(X1,X2),X1)
      | k2_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f34,f29])).

fof(f377,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f95,f374])).

fof(f95,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f28,f43])).

fof(f28,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f16])).

fof(f16,plain,
    ( ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))
   => ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:11:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (812089344)
% 0.14/0.37  ipcrm: permission denied for id (814088194)
% 0.14/0.37  ipcrm: permission denied for id (812122115)
% 0.14/0.38  ipcrm: permission denied for id (814252040)
% 0.14/0.38  ipcrm: permission denied for id (814284809)
% 0.14/0.39  ipcrm: permission denied for id (814383116)
% 0.22/0.39  ipcrm: permission denied for id (814514192)
% 0.22/0.39  ipcrm: permission denied for id (814579730)
% 0.22/0.39  ipcrm: permission denied for id (812351507)
% 0.22/0.40  ipcrm: permission denied for id (814645269)
% 0.22/0.40  ipcrm: permission denied for id (814678038)
% 0.22/0.40  ipcrm: permission denied for id (812384279)
% 0.22/0.40  ipcrm: permission denied for id (814710808)
% 0.22/0.40  ipcrm: permission denied for id (814743577)
% 0.22/0.40  ipcrm: permission denied for id (814809115)
% 0.22/0.40  ipcrm: permission denied for id (812417052)
% 0.22/0.41  ipcrm: permission denied for id (814841885)
% 0.22/0.41  ipcrm: permission denied for id (812449822)
% 0.22/0.41  ipcrm: permission denied for id (814940193)
% 0.22/0.41  ipcrm: permission denied for id (812515362)
% 0.22/0.41  ipcrm: permission denied for id (814972963)
% 0.22/0.42  ipcrm: permission denied for id (812580902)
% 0.22/0.42  ipcrm: permission denied for id (815136809)
% 0.22/0.42  ipcrm: permission denied for id (812646442)
% 0.22/0.42  ipcrm: permission denied for id (815169579)
% 0.22/0.42  ipcrm: permission denied for id (815202348)
% 0.22/0.43  ipcrm: permission denied for id (815235117)
% 0.22/0.43  ipcrm: permission denied for id (815267886)
% 0.22/0.43  ipcrm: permission denied for id (815366193)
% 0.22/0.43  ipcrm: permission denied for id (812744754)
% 0.22/0.43  ipcrm: permission denied for id (815431732)
% 0.22/0.44  ipcrm: permission denied for id (812843063)
% 0.22/0.44  ipcrm: permission denied for id (815530040)
% 0.22/0.44  ipcrm: permission denied for id (815562809)
% 0.22/0.44  ipcrm: permission denied for id (815595578)
% 0.22/0.44  ipcrm: permission denied for id (815661116)
% 0.22/0.45  ipcrm: permission denied for id (815726654)
% 0.22/0.45  ipcrm: permission denied for id (813039680)
% 0.22/0.45  ipcrm: permission denied for id (813105219)
% 0.22/0.45  ipcrm: permission denied for id (815857732)
% 0.22/0.46  ipcrm: permission denied for id (813137989)
% 0.22/0.46  ipcrm: permission denied for id (813170759)
% 0.22/0.46  ipcrm: permission denied for id (813203528)
% 0.22/0.46  ipcrm: permission denied for id (815956042)
% 0.22/0.46  ipcrm: permission denied for id (815988811)
% 0.22/0.46  ipcrm: permission denied for id (816021580)
% 0.22/0.47  ipcrm: permission denied for id (813269070)
% 0.22/0.47  ipcrm: permission denied for id (813301839)
% 0.22/0.47  ipcrm: permission denied for id (816185426)
% 0.22/0.47  ipcrm: permission denied for id (816218195)
% 0.22/0.48  ipcrm: permission denied for id (816283733)
% 0.22/0.48  ipcrm: permission denied for id (813367382)
% 0.22/0.48  ipcrm: permission denied for id (816316503)
% 0.22/0.48  ipcrm: permission denied for id (816382041)
% 0.22/0.48  ipcrm: permission denied for id (816447579)
% 0.22/0.48  ipcrm: permission denied for id (816513117)
% 0.22/0.49  ipcrm: permission denied for id (813498466)
% 0.22/0.49  ipcrm: permission denied for id (816709732)
% 0.22/0.50  ipcrm: permission denied for id (813596774)
% 0.22/0.50  ipcrm: permission denied for id (816840808)
% 0.22/0.50  ipcrm: permission denied for id (816939115)
% 0.22/0.50  ipcrm: permission denied for id (813727853)
% 0.22/0.51  ipcrm: permission denied for id (813760623)
% 0.22/0.51  ipcrm: permission denied for id (817102962)
% 0.22/0.51  ipcrm: permission denied for id (813826164)
% 0.22/0.51  ipcrm: permission denied for id (813858933)
% 0.22/0.52  ipcrm: permission denied for id (817168502)
% 0.36/0.52  ipcrm: permission denied for id (817332347)
% 0.36/0.52  ipcrm: permission denied for id (813957244)
% 0.36/0.53  ipcrm: permission denied for id (817397886)
% 0.36/0.53  ipcrm: permission denied for id (814022783)
% 0.40/0.66  % (4362)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.40/0.68  % (4355)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.40/0.69  % (4353)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.40/0.69  % (4373)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.40/0.70  % (4358)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.40/0.70  % (4378)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.40/0.70  % (4366)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.40/0.70  % (4375)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.40/0.70  % (4370)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.40/0.71  % (4368)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.40/0.71  % (4353)Refutation not found, incomplete strategy% (4353)------------------------------
% 0.40/0.71  % (4353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.40/0.71  % (4364)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.40/0.71  % (4353)Termination reason: Refutation not found, incomplete strategy
% 0.40/0.71  
% 0.40/0.71  % (4353)Memory used [KB]: 10618
% 0.40/0.71  % (4353)Time elapsed: 0.116 s
% 0.40/0.71  % (4353)------------------------------
% 0.40/0.71  % (4353)------------------------------
% 0.40/0.71  % (4373)Refutation not found, incomplete strategy% (4373)------------------------------
% 0.40/0.71  % (4373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.40/0.71  % (4373)Termination reason: Refutation not found, incomplete strategy
% 0.40/0.71  
% 0.40/0.71  % (4373)Memory used [KB]: 10618
% 0.40/0.71  % (4373)Time elapsed: 0.139 s
% 0.40/0.71  % (4373)------------------------------
% 0.40/0.71  % (4373)------------------------------
% 0.40/0.71  % (4365)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.40/0.71  % (4367)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.40/0.71  % (4369)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.40/0.72  % (4360)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.40/0.72  % (4351)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.40/0.72  % (4359)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.40/0.72  % (4352)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.40/0.72  % (4380)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.40/0.72  % (4359)Refutation not found, incomplete strategy% (4359)------------------------------
% 0.40/0.72  % (4359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.40/0.72  % (4354)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.40/0.72  % (4376)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.40/0.72  % (4359)Termination reason: Refutation not found, incomplete strategy
% 0.40/0.72  
% 0.40/0.72  % (4359)Memory used [KB]: 10618
% 0.40/0.72  % (4359)Time elapsed: 0.151 s
% 0.40/0.72  % (4374)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.40/0.72  % (4359)------------------------------
% 0.40/0.72  % (4359)------------------------------
% 0.40/0.73  % (4361)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.40/0.73  % (4371)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.40/0.73  % (4361)Refutation not found, incomplete strategy% (4361)------------------------------
% 0.40/0.73  % (4361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.40/0.73  % (4361)Termination reason: Refutation not found, incomplete strategy
% 0.40/0.73  
% 0.40/0.73  % (4361)Memory used [KB]: 10618
% 0.40/0.73  % (4361)Time elapsed: 0.163 s
% 0.40/0.73  % (4361)------------------------------
% 0.40/0.73  % (4361)------------------------------
% 0.40/0.73  % (4356)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.40/0.74  % (4357)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.40/0.74  % (4377)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.40/0.74  % (4379)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.40/0.75  % (4363)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.60/0.76  % (4372)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.60/0.83  % (4358)Refutation found. Thanks to Tanya!
% 0.60/0.83  % SZS status Theorem for theBenchmark
% 0.60/0.84  % SZS output start Proof for theBenchmark
% 0.60/0.84  fof(f992,plain,(
% 0.60/0.84    $false),
% 0.60/0.84    inference(subsumption_resolution,[],[f377,f970])).
% 0.60/0.84  fof(f970,plain,(
% 0.60/0.84    ( ! [X23,X22] : (r1_tarski(k1_zfmisc_1(k4_xboole_0(X22,X23)),k1_zfmisc_1(k5_xboole_0(X23,X22)))) )),
% 0.60/0.84    inference(superposition,[],[f374,f961])).
% 0.60/0.84  fof(f961,plain,(
% 0.60/0.84    ( ! [X14,X13] : (k5_xboole_0(X13,X14) = k5_xboole_0(X14,X13)) )),
% 0.60/0.84    inference(subsumption_resolution,[],[f959,f951])).
% 0.60/0.84  fof(f951,plain,(
% 0.60/0.84    ( ! [X2,X3] : (r1_tarski(k5_xboole_0(X3,X2),k5_xboole_0(X2,X3))) )),
% 0.60/0.84    inference(subsumption_resolution,[],[f931,f70])).
% 0.60/0.84  fof(f70,plain,(
% 0.60/0.84    ( ! [X6,X5] : (r1_tarski(k4_xboole_0(X5,X6),k5_xboole_0(X5,X6))) )),
% 0.60/0.84    inference(superposition,[],[f29,f31])).
% 0.60/0.84  fof(f31,plain,(
% 0.60/0.84    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.60/0.84    inference(cnf_transformation,[],[f2])).
% 0.60/0.84  % (4415)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 0.60/0.84  fof(f2,axiom,(
% 0.60/0.84    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.60/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.60/0.84  fof(f29,plain,(
% 0.60/0.84    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.60/0.84    inference(cnf_transformation,[],[f5])).
% 0.60/0.84  fof(f5,axiom,(
% 0.60/0.84    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.60/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.60/0.84  fof(f931,plain,(
% 0.60/0.84    ( ! [X2,X3] : (~r1_tarski(k4_xboole_0(X2,X3),k5_xboole_0(X2,X3)) | r1_tarski(k5_xboole_0(X3,X2),k5_xboole_0(X2,X3))) )),
% 0.60/0.84    inference(resolution,[],[f78,f72])).
% 0.60/0.84  fof(f72,plain,(
% 0.60/0.84    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X1,X0))) )),
% 0.60/0.84    inference(resolution,[],[f69,f44])).
% 0.60/0.84  fof(f44,plain,(
% 0.60/0.84    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.60/0.84    inference(equality_resolution,[],[f33])).
% 0.60/0.84  fof(f33,plain,(
% 0.60/0.84    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.60/0.84    inference(cnf_transformation,[],[f19])).
% 0.60/0.84  fof(f19,plain,(
% 0.60/0.84    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.60/0.84    inference(flattening,[],[f18])).
% 0.60/0.84  fof(f18,plain,(
% 0.60/0.84    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.60/0.84    inference(nnf_transformation,[],[f3])).
% 0.60/0.84  fof(f3,axiom,(
% 0.60/0.84    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.60/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.60/0.84  fof(f69,plain,(
% 0.60/0.84    ( ! [X4,X2,X3] : (~r1_tarski(X4,k4_xboole_0(X3,X2)) | r1_tarski(X4,k5_xboole_0(X2,X3))) )),
% 0.60/0.84    inference(superposition,[],[f42,f31])).
% 0.60/0.84  fof(f42,plain,(
% 0.60/0.84    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.60/0.84    inference(cnf_transformation,[],[f13])).
% 0.60/0.84  fof(f13,plain,(
% 0.60/0.84    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.60/0.84    inference(ennf_transformation,[],[f4])).
% 0.60/0.84  fof(f4,axiom,(
% 0.60/0.84    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.60/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.60/0.84  fof(f78,plain,(
% 0.60/0.84    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(k4_xboole_0(X1,X0),X2) | r1_tarski(k5_xboole_0(X0,X1),X2)) )),
% 0.60/0.84    inference(superposition,[],[f43,f31])).
% 0.60/0.84  fof(f43,plain,(
% 0.60/0.84    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.60/0.84    inference(cnf_transformation,[],[f15])).
% 0.60/0.84  fof(f15,plain,(
% 0.60/0.84    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.60/0.84    inference(flattening,[],[f14])).
% 0.60/0.84  fof(f14,plain,(
% 0.60/0.84    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.60/0.84    inference(ennf_transformation,[],[f6])).
% 0.60/0.84  fof(f6,axiom,(
% 0.60/0.84    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.60/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.60/0.84  fof(f959,plain,(
% 0.60/0.84    ( ! [X14,X13] : (~r1_tarski(k5_xboole_0(X13,X14),k5_xboole_0(X14,X13)) | k5_xboole_0(X13,X14) = k5_xboole_0(X14,X13)) )),
% 0.60/0.84    inference(resolution,[],[f951,f34])).
% 0.60/0.84  fof(f34,plain,(
% 0.60/0.84    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.60/0.84    inference(cnf_transformation,[],[f19])).
% 0.60/0.84  fof(f374,plain,(
% 0.60/0.84    ( ! [X6,X5] : (r1_tarski(k1_zfmisc_1(k4_xboole_0(X5,X6)),k1_zfmisc_1(k5_xboole_0(X5,X6)))) )),
% 0.60/0.84    inference(superposition,[],[f363,f31])).
% 0.60/0.84  fof(f363,plain,(
% 0.60/0.84    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(k2_xboole_0(X0,X1)))) )),
% 0.60/0.84    inference(duplicate_literal_removal,[],[f352])).
% 0.60/0.84  fof(f352,plain,(
% 0.60/0.84    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(k2_xboole_0(X0,X1))) | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(k2_xboole_0(X0,X1)))) )),
% 0.60/0.84    inference(resolution,[],[f114,f51])).
% 0.60/0.84  fof(f51,plain,(
% 0.60/0.84    ( ! [X2,X1] : (~r1_tarski(sK2(X1,k1_zfmisc_1(X2)),X2) | r1_tarski(X1,k1_zfmisc_1(X2))) )),
% 0.60/0.84    inference(resolution,[],[f37,f46])).
% 0.60/0.84  fof(f46,plain,(
% 0.60/0.84    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.60/0.84    inference(equality_resolution,[],[f39])).
% 0.60/0.84  fof(f39,plain,(
% 0.60/0.84    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.60/0.84    inference(cnf_transformation,[],[f27])).
% 0.60/0.84  fof(f27,plain,(
% 0.60/0.84    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.60/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).
% 0.60/0.84  fof(f26,plain,(
% 0.60/0.84    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.60/0.84    introduced(choice_axiom,[])).
% 0.60/0.84  fof(f25,plain,(
% 0.60/0.84    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.60/0.84    inference(rectify,[],[f24])).
% 0.60/0.84  fof(f24,plain,(
% 0.60/0.84    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.60/0.84    inference(nnf_transformation,[],[f7])).
% 0.60/0.84  fof(f7,axiom,(
% 0.60/0.84    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.60/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.60/0.84  fof(f37,plain,(
% 0.60/0.84    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.60/0.84    inference(cnf_transformation,[],[f23])).
% 0.60/0.84  fof(f23,plain,(
% 0.60/0.84    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.60/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).
% 0.60/0.84  fof(f22,plain,(
% 0.60/0.84    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.60/0.84    introduced(choice_axiom,[])).
% 0.60/0.84  fof(f21,plain,(
% 0.60/0.84    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.60/0.84    inference(rectify,[],[f20])).
% 0.60/0.84  fof(f20,plain,(
% 0.60/0.84    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.60/0.84    inference(nnf_transformation,[],[f12])).
% 0.60/0.84  fof(f12,plain,(
% 0.60/0.84    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.60/0.84    inference(ennf_transformation,[],[f1])).
% 0.60/0.84  fof(f1,axiom,(
% 0.60/0.84    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.60/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.60/0.84  fof(f114,plain,(
% 0.60/0.84    ( ! [X21,X19,X20] : (r1_tarski(sK2(k1_zfmisc_1(X19),X20),k2_xboole_0(X19,X21)) | r1_tarski(k1_zfmisc_1(X19),X20)) )),
% 0.60/0.84    inference(resolution,[],[f106,f49])).
% 0.60/0.84  fof(f49,plain,(
% 0.60/0.84    ( ! [X0,X1] : (r1_tarski(sK2(k1_zfmisc_1(X0),X1),X0) | r1_tarski(k1_zfmisc_1(X0),X1)) )),
% 0.60/0.84    inference(resolution,[],[f36,f47])).
% 0.60/0.84  fof(f47,plain,(
% 0.60/0.84    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 0.60/0.84    inference(equality_resolution,[],[f38])).
% 0.60/0.84  fof(f38,plain,(
% 0.60/0.84    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.60/0.84    inference(cnf_transformation,[],[f27])).
% 0.60/0.84  fof(f36,plain,(
% 0.60/0.84    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.60/0.84    inference(cnf_transformation,[],[f23])).
% 0.60/0.84  fof(f106,plain,(
% 0.60/0.84    ( ! [X6,X7,X5] : (~r1_tarski(X7,X5) | r1_tarski(X7,k2_xboole_0(X5,X6))) )),
% 0.60/0.84    inference(superposition,[],[f42,f81])).
% 0.60/0.84  fof(f81,plain,(
% 0.60/0.84    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k2_xboole_0(k2_xboole_0(X1,X2),X1)) )),
% 0.60/0.84    inference(resolution,[],[f79,f29])).
% 0.60/0.84  fof(f79,plain,(
% 0.60/0.84    ( ! [X4,X3] : (~r1_tarski(X3,X4) | k2_xboole_0(X4,X3) = X4) )),
% 0.60/0.84    inference(subsumption_resolution,[],[f76,f44])).
% 0.60/0.84  fof(f76,plain,(
% 0.60/0.84    ( ! [X4,X3] : (~r1_tarski(X3,X4) | ~r1_tarski(X4,X4) | k2_xboole_0(X4,X3) = X4) )),
% 0.60/0.84    inference(resolution,[],[f43,f54])).
% 0.60/0.84  fof(f54,plain,(
% 0.60/0.84    ( ! [X2,X1] : (~r1_tarski(k2_xboole_0(X1,X2),X1) | k2_xboole_0(X1,X2) = X1) )),
% 0.60/0.84    inference(resolution,[],[f34,f29])).
% 0.60/0.84  fof(f377,plain,(
% 0.60/0.84    ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.60/0.84    inference(subsumption_resolution,[],[f95,f374])).
% 0.60/0.84  fof(f95,plain,(
% 0.60/0.84    ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.60/0.84    inference(resolution,[],[f28,f43])).
% 0.60/0.84  fof(f28,plain,(
% 0.60/0.84    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.60/0.84    inference(cnf_transformation,[],[f17])).
% 0.60/0.84  fof(f17,plain,(
% 0.60/0.84    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.60/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f16])).
% 0.60/0.84  fof(f16,plain,(
% 0.60/0.84    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) => ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.60/0.84    introduced(choice_axiom,[])).
% 0.60/0.84  fof(f11,plain,(
% 0.60/0.84    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 0.60/0.84    inference(ennf_transformation,[],[f10])).
% 0.60/0.84  fof(f10,negated_conjecture,(
% 0.60/0.84    ~! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 0.60/0.84    inference(negated_conjecture,[],[f9])).
% 0.60/0.84  fof(f9,conjecture,(
% 0.60/0.84    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 0.60/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_zfmisc_1)).
% 0.60/0.84  % SZS output end Proof for theBenchmark
% 0.60/0.84  % (4358)------------------------------
% 0.60/0.84  % (4358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.60/0.84  % (4358)Termination reason: Refutation
% 0.60/0.84  
% 0.60/0.84  % (4358)Memory used [KB]: 7419
% 0.60/0.84  % (4358)Time elapsed: 0.231 s
% 0.60/0.84  % (4358)------------------------------
% 0.60/0.84  % (4358)------------------------------
% 0.60/0.84  % (4214)Success in time 0.477 s
%------------------------------------------------------------------------------
