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
% DateTime   : Thu Dec  3 12:55:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 420 expanded)
%              Number of leaves         :   14 ( 119 expanded)
%              Depth                    :   21
%              Number of atoms          :  307 (2314 expanded)
%              Number of equality atoms :   14 ( 154 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f388,plain,(
    $false ),
    inference(resolution,[],[f380,f120])).

fof(f120,plain,(
    ! [X1] : ~ r2_hidden(sK3(sK3(X1)),X1) ),
    inference(resolution,[],[f115,f46])).

fof(f46,plain,(
    ! [X0] : r2_hidden(X0,sK3(X0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X2] :
          ( r2_hidden(k1_zfmisc_1(X2),sK3(X0))
          | ~ r2_hidden(X2,sK3(X0)) )
      & ! [X3,X4] :
          ( r2_hidden(X4,sK3(X0))
          | ~ r1_tarski(X4,X3)
          | ~ r2_hidden(X3,sK3(X0)) )
      & r2_hidden(X0,sK3(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_zfmisc_1(X2),X1)
              | ~ r2_hidden(X2,X1) )
          & ! [X3,X4] :
              ( r2_hidden(X4,X1)
              | ~ r1_tarski(X4,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X0,X1) )
     => ( ! [X2] :
            ( r2_hidden(k1_zfmisc_1(X2),sK3(X0))
            | ~ r2_hidden(X2,sK3(X0)) )
        & ! [X4,X3] :
            ( r2_hidden(X4,sK3(X0))
            | ~ r1_tarski(X4,X3)
            | ~ r2_hidden(X3,sK3(X0)) )
        & r2_hidden(X0,sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(k1_zfmisc_1(X2),X1)
          | ~ r2_hidden(X2,X1) )
      & ! [X3,X4] :
          ( r2_hidden(X4,X1)
          | ~ r1_tarski(X4,X3)
          | ~ r2_hidden(X3,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X3] :
          ( r2_hidden(k1_zfmisc_1(X3),X1)
          | ~ r2_hidden(X3,X1) )
      & ! [X4,X5] :
          ( r2_hidden(X5,X1)
          | ~ r1_tarski(X5,X4)
          | ~ r2_hidden(X4,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X3] :
          ( r2_hidden(k1_zfmisc_1(X3),X1)
          | ~ r2_hidden(X3,X1) )
      & ! [X4,X5] :
          ( r2_hidden(X5,X1)
          | ~ r1_tarski(X5,X4)
          | ~ r2_hidden(X4,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(k1_zfmisc_1(X3),X1) )
      & ! [X4,X5] :
          ( ( r1_tarski(X5,X4)
            & r2_hidden(X4,X1) )
         => r2_hidden(X5,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & ~ r2_tarski(X2,X1)
            & r1_tarski(X2,X1) )
      & ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(k1_zfmisc_1(X3),X1) )
      & ! [X4,X5] :
          ( ( r1_tarski(X5,X4)
            & r2_hidden(X4,X1) )
         => r2_hidden(X5,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & ~ r2_tarski(X2,X1)
            & r1_tarski(X2,X1) )
      & ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(k1_zfmisc_1(X2),X1) )
      & ! [X2,X3] :
          ( ( r1_tarski(X3,X2)
            & r2_hidden(X2,X1) )
         => r2_hidden(X3,X1) )
      & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_zfmisc_1)).

fof(f115,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(sK3(X13),X12)
      | ~ r2_hidden(X12,X13) ) ),
    inference(resolution,[],[f57,f46])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X2,X0)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_ordinal1)).

fof(f380,plain,(
    ! [X0] : r2_hidden(X0,sK3(k1_setfam_1(sK0))) ),
    inference(resolution,[],[f379,f185])).

fof(f185,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X0,sK3(X1)) ) ),
    inference(resolution,[],[f47,f46])).

fof(f47,plain,(
    ! [X4,X0,X3] :
      ( ~ r2_hidden(X3,sK3(X0))
      | ~ r1_tarski(X4,X3)
      | r2_hidden(X4,sK3(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f379,plain,(
    ! [X32] : r1_tarski(X32,k1_setfam_1(sK0)) ),
    inference(subsumption_resolution,[],[f375,f301])).

fof(f301,plain,(
    ! [X14,X15] :
      ( r2_hidden(sK4(sK0,X14),X15)
      | r1_tarski(X14,k1_setfam_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f281,f41])).

fof(f41,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ! [X2] :
        ( ( ~ r1_ordinal1(X2,sK2(X2))
          & r2_hidden(sK2(X2),sK0)
          & v3_ordinal1(sK2(X2)) )
        | ~ r2_hidden(X2,sK0)
        | ~ v3_ordinal1(X2) )
    & k1_xboole_0 != sK0
    & r1_tarski(sK0,sK1)
    & v3_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f26,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ? [X3] :
                ( ~ r1_ordinal1(X2,X3)
                & r2_hidden(X3,X0)
                & v3_ordinal1(X3) )
            | ~ r2_hidden(X2,X0)
            | ~ v3_ordinal1(X2) )
        & k1_xboole_0 != X0
        & r1_tarski(X0,X1)
        & v3_ordinal1(X1) )
   => ( ! [X2] :
          ( ? [X3] :
              ( ~ r1_ordinal1(X2,X3)
              & r2_hidden(X3,sK0)
              & v3_ordinal1(X3) )
          | ~ r2_hidden(X2,sK0)
          | ~ v3_ordinal1(X2) )
      & k1_xboole_0 != sK0
      & r1_tarski(sK0,sK1)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X2] :
      ( ? [X3] :
          ( ~ r1_ordinal1(X2,X3)
          & r2_hidden(X3,sK0)
          & v3_ordinal1(X3) )
     => ( ~ r1_ordinal1(X2,sK2(X2))
        & r2_hidden(sK2(X2),sK0)
        & v3_ordinal1(sK2(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ~ r1_ordinal1(X2,X3)
              & r2_hidden(X3,X0)
              & v3_ordinal1(X3) )
          | ~ r2_hidden(X2,X0)
          | ~ v3_ordinal1(X2) )
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ~ r1_ordinal1(X2,X3)
              & r2_hidden(X3,X0)
              & v3_ordinal1(X3) )
          | ~ r2_hidden(X2,X0)
          | ~ v3_ordinal1(X2) )
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v3_ordinal1(X1)
       => ~ ( ! [X2] :
                ( v3_ordinal1(X2)
               => ~ ( ! [X3] :
                        ( v3_ordinal1(X3)
                       => ( r2_hidden(X3,X0)
                         => r1_ordinal1(X2,X3) ) )
                    & r2_hidden(X2,X0) ) )
            & k1_xboole_0 != X0
            & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ~ ( ! [X2] :
              ( v3_ordinal1(X2)
             => ~ ( ! [X3] :
                      ( v3_ordinal1(X3)
                     => ( r2_hidden(X3,X0)
                       => r1_ordinal1(X2,X3) ) )
                  & r2_hidden(X2,X0) ) )
          & k1_xboole_0 != X0
          & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_ordinal1)).

fof(f281,plain,(
    ! [X14,X15] :
      ( k1_xboole_0 = sK0
      | r1_tarski(X14,k1_setfam_1(sK0))
      | r2_hidden(sK4(sK0,X14),X15) ) ),
    inference(resolution,[],[f50,f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f145,f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f145,plain,(
    ! [X0] : r1_tarski(sK0,X0) ),
    inference(subsumption_resolution,[],[f144,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0),X0) ) ),
    inference(resolution,[],[f53,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK6(X1),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK6(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK6(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f23,f37])).

fof(f37,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK6(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK6(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f144,plain,(
    ! [X0] :
      ( r1_tarski(sK0,X0)
      | ~ r2_hidden(sK6(sK0),sK0) ) ),
    inference(subsumption_resolution,[],[f143,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | v3_ordinal1(X0) ) ),
    inference(resolution,[],[f78,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | v3_ordinal1(X0) ) ),
    inference(resolution,[],[f49,f39])).

fof(f39,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f27])).

% (24565)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r2_hidden(X0,X1)
      | v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f78,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f52,f40])).

fof(f40,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f143,plain,(
    ! [X0] :
      ( r1_tarski(sK0,X0)
      | ~ r2_hidden(sK6(sK0),sK0)
      | ~ v3_ordinal1(sK6(sK0)) ) ),
    inference(resolution,[],[f139,f43])).

fof(f43,plain,(
    ! [X2] :
      ( r2_hidden(sK2(X2),sK0)
      | ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f139,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(sK6(sK0)),sK0)
      | r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f137,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK6(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(condensation,[],[f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK6(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f137,plain,(
    ! [X2] :
      ( r2_hidden(sK2(sK6(sK0)),sK6(sK0))
      | r1_tarski(sK0,X2) ) ),
    inference(resolution,[],[f134,f62])).

fof(f134,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(subsumption_resolution,[],[f133,f86])).

fof(f86,plain,(
    ! [X2] :
      ( v3_ordinal1(sK2(X2))
      | ~ r2_hidden(X2,sK0) ) ),
    inference(subsumption_resolution,[],[f42,f82])).

fof(f42,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | v3_ordinal1(sK2(X2))
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f133,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | ~ v3_ordinal1(sK2(X0))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f132,f82])).

fof(f132,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | ~ v3_ordinal1(sK2(X0))
      | ~ v3_ordinal1(X0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | ~ v3_ordinal1(sK2(X0))
      | ~ v3_ordinal1(X0)
      | ~ r2_hidden(X0,sK0)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f45,f44])).

fof(f44,plain,(
    ! [X2] :
      ( ~ r1_ordinal1(X2,sK2(X2))
      | ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f31])).

% (24558)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f375,plain,(
    ! [X33,X32] :
      ( r1_tarski(X32,k1_setfam_1(sK0))
      | ~ r2_hidden(sK4(sK0,X32),X33) ) ),
    inference(resolution,[],[f301,f58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:16:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (24555)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (24563)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (24547)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (24546)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (24540)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (24545)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (24544)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (24541)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (24544)Refutation not found, incomplete strategy% (24544)------------------------------
% 0.21/0.54  % (24544)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24544)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24544)Memory used [KB]: 6140
% 0.21/0.54  % (24544)Time elapsed: 0.116 s
% 0.21/0.54  % (24544)------------------------------
% 0.21/0.54  % (24544)------------------------------
% 0.21/0.54  % (24567)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (24569)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (24542)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (24562)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (24560)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (24543)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (24552)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (24566)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (24559)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (24547)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % (24554)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f388,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(resolution,[],[f380,f120])).
% 0.21/0.55  fof(f120,plain,(
% 0.21/0.55    ( ! [X1] : (~r2_hidden(sK3(sK3(X1)),X1)) )),
% 0.21/0.55    inference(resolution,[],[f115,f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(X0,sK3(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X0] : (! [X2] : (r2_hidden(k1_zfmisc_1(X2),sK3(X0)) | ~r2_hidden(X2,sK3(X0))) & ! [X3,X4] : (r2_hidden(X4,sK3(X0)) | ~r1_tarski(X4,X3) | ~r2_hidden(X3,sK3(X0))) & r2_hidden(X0,sK3(X0)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0] : (? [X1] : (! [X2] : (r2_hidden(k1_zfmisc_1(X2),X1) | ~r2_hidden(X2,X1)) & ! [X3,X4] : (r2_hidden(X4,X1) | ~r1_tarski(X4,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X0,X1)) => (! [X2] : (r2_hidden(k1_zfmisc_1(X2),sK3(X0)) | ~r2_hidden(X2,sK3(X0))) & ! [X4,X3] : (r2_hidden(X4,sK3(X0)) | ~r1_tarski(X4,X3) | ~r2_hidden(X3,sK3(X0))) & r2_hidden(X0,sK3(X0))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(k1_zfmisc_1(X2),X1) | ~r2_hidden(X2,X1)) & ! [X3,X4] : (r2_hidden(X4,X1) | ~r1_tarski(X4,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X0,X1))),
% 0.21/0.55    inference(rectify,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0] : ? [X1] : (! [X3] : (r2_hidden(k1_zfmisc_1(X3),X1) | ~r2_hidden(X3,X1)) & ! [X4,X5] : (r2_hidden(X5,X1) | ~r1_tarski(X5,X4) | ~r2_hidden(X4,X1)) & r2_hidden(X0,X1))),
% 0.21/0.55    inference(flattening,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0] : ? [X1] : (! [X3] : (r2_hidden(k1_zfmisc_1(X3),X1) | ~r2_hidden(X3,X1)) & ! [X4,X5] : (r2_hidden(X5,X1) | (~r1_tarski(X5,X4) | ~r2_hidden(X4,X1))) & r2_hidden(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,plain,(
% 0.21/0.55    ! [X0] : ? [X1] : (! [X3] : (r2_hidden(X3,X1) => r2_hidden(k1_zfmisc_1(X3),X1)) & ! [X4,X5] : ((r1_tarski(X5,X4) & r2_hidden(X4,X1)) => r2_hidden(X5,X1)) & r2_hidden(X0,X1))),
% 0.21/0.55    inference(pure_predicate_removal,[],[f10])).
% 0.21/0.55  fof(f10,plain,(
% 0.21/0.55    ! [X0] : ? [X1] : (! [X2] : ~(~r2_hidden(X2,X1) & ~r2_tarski(X2,X1) & r1_tarski(X2,X1)) & ! [X3] : (r2_hidden(X3,X1) => r2_hidden(k1_zfmisc_1(X3),X1)) & ! [X4,X5] : ((r1_tarski(X5,X4) & r2_hidden(X4,X1)) => r2_hidden(X5,X1)) & r2_hidden(X0,X1))),
% 0.21/0.55    inference(rectify,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0] : ? [X1] : (! [X2] : ~(~r2_hidden(X2,X1) & ~r2_tarski(X2,X1) & r1_tarski(X2,X1)) & ! [X2] : (r2_hidden(X2,X1) => r2_hidden(k1_zfmisc_1(X2),X1)) & ! [X2,X3] : ((r1_tarski(X3,X2) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)) & r2_hidden(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_zfmisc_1)).
% 0.21/0.55  fof(f115,plain,(
% 0.21/0.55    ( ! [X12,X13] : (~r2_hidden(sK3(X13),X12) | ~r2_hidden(X12,X13)) )),
% 0.21/0.55    inference(resolution,[],[f57,f46])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (~r2_hidden(X2,X0) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ~(r2_hidden(X2,X0) & r2_hidden(X1,X2) & r2_hidden(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_ordinal1)).
% 0.21/0.55  fof(f380,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(X0,sK3(k1_setfam_1(sK0)))) )),
% 0.21/0.55    inference(resolution,[],[f379,f185])).
% 0.21/0.55  fof(f185,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X0,sK3(X1))) )),
% 0.21/0.55    inference(resolution,[],[f47,f46])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ( ! [X4,X0,X3] : (~r2_hidden(X3,sK3(X0)) | ~r1_tarski(X4,X3) | r2_hidden(X4,sK3(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f30])).
% 0.21/0.55  fof(f379,plain,(
% 0.21/0.55    ( ! [X32] : (r1_tarski(X32,k1_setfam_1(sK0))) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f375,f301])).
% 0.21/0.55  fof(f301,plain,(
% 0.21/0.55    ( ! [X14,X15] : (r2_hidden(sK4(sK0,X14),X15) | r1_tarski(X14,k1_setfam_1(sK0))) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f281,f41])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    k1_xboole_0 != sK0),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X2] : ((~r1_ordinal1(X2,sK2(X2)) & r2_hidden(sK2(X2),sK0) & v3_ordinal1(sK2(X2))) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) & k1_xboole_0 != sK0 & r1_tarski(sK0,sK1) & v3_ordinal1(sK1)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f26,f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ? [X0,X1] : (! [X2] : (? [X3] : (~r1_ordinal1(X2,X3) & r2_hidden(X3,X0) & v3_ordinal1(X3)) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) & k1_xboole_0 != X0 & r1_tarski(X0,X1) & v3_ordinal1(X1)) => (! [X2] : (? [X3] : (~r1_ordinal1(X2,X3) & r2_hidden(X3,sK0) & v3_ordinal1(X3)) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) & k1_xboole_0 != sK0 & r1_tarski(sK0,sK1) & v3_ordinal1(sK1))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X2] : (? [X3] : (~r1_ordinal1(X2,X3) & r2_hidden(X3,sK0) & v3_ordinal1(X3)) => (~r1_ordinal1(X2,sK2(X2)) & r2_hidden(sK2(X2),sK0) & v3_ordinal1(sK2(X2))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ? [X0,X1] : (! [X2] : (? [X3] : (~r1_ordinal1(X2,X3) & r2_hidden(X3,X0) & v3_ordinal1(X3)) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) & k1_xboole_0 != X0 & r1_tarski(X0,X1) & v3_ordinal1(X1))),
% 0.21/0.55    inference(flattening,[],[f12])).
% 0.21/0.55  fof(f12,plain,(
% 0.21/0.55    ? [X0,X1] : ((! [X2] : ((? [X3] : ((~r1_ordinal1(X2,X3) & r2_hidden(X3,X0)) & v3_ordinal1(X3)) | ~r2_hidden(X2,X0)) | ~v3_ordinal1(X2)) & k1_xboole_0 != X0 & r1_tarski(X0,X1)) & v3_ordinal1(X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1] : (v3_ordinal1(X1) => ~(! [X2] : (v3_ordinal1(X2) => ~(! [X3] : (v3_ordinal1(X3) => (r2_hidden(X3,X0) => r1_ordinal1(X2,X3))) & r2_hidden(X2,X0))) & k1_xboole_0 != X0 & r1_tarski(X0,X1)))),
% 0.21/0.55    inference(negated_conjecture,[],[f8])).
% 0.21/0.55  fof(f8,conjecture,(
% 0.21/0.55    ! [X0,X1] : (v3_ordinal1(X1) => ~(! [X2] : (v3_ordinal1(X2) => ~(! [X3] : (v3_ordinal1(X3) => (r2_hidden(X3,X0) => r1_ordinal1(X2,X3))) & r2_hidden(X2,X0))) & k1_xboole_0 != X0 & r1_tarski(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_ordinal1)).
% 0.21/0.55  fof(f281,plain,(
% 0.21/0.55    ( ! [X14,X15] : (k1_xboole_0 = sK0 | r1_tarski(X14,k1_setfam_1(sK0)) | r2_hidden(sK4(sK0,X14),X15)) )),
% 0.21/0.55    inference(resolution,[],[f50,f146])).
% 0.21/0.55  fof(f146,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | r2_hidden(X0,X1)) )),
% 0.21/0.55    inference(resolution,[],[f145,f52])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(rectify,[],[f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(nnf_transformation,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.55  fof(f145,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(sK0,X0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f144,f62])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK6(X0),X0)) )),
% 0.21/0.55    inference(resolution,[],[f53,f55])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(sK6(X1),X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK6(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK6(X1),X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f23,f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK6(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK6(X1),X1)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f36])).
% 0.21/0.55  fof(f144,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(sK0,X0) | ~r2_hidden(sK6(sK0),sK0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f143,f82])).
% 0.21/0.55  fof(f82,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,sK0) | v3_ordinal1(X0)) )),
% 0.21/0.55    inference(resolution,[],[f78,f59])).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,sK1) | v3_ordinal1(X0)) )),
% 0.21/0.55    inference(resolution,[],[f49,f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    v3_ordinal1(sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  % (24565)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r2_hidden(X0,X1) | v3_ordinal1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 0.21/0.55    inference(flattening,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).
% 0.21/0.55  fof(f78,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 0.21/0.55    inference(resolution,[],[f52,f40])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    r1_tarski(sK0,sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f143,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(sK0,X0) | ~r2_hidden(sK6(sK0),sK0) | ~v3_ordinal1(sK6(sK0))) )),
% 0.21/0.55    inference(resolution,[],[f139,f43])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ( ! [X2] : (r2_hidden(sK2(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f139,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(sK2(sK6(sK0)),sK0) | r1_tarski(sK0,X0)) )),
% 0.21/0.55    inference(resolution,[],[f137,f58])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X0,sK6(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.55    inference(condensation,[],[f56])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK6(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f38])).
% 0.21/0.55  fof(f137,plain,(
% 0.21/0.55    ( ! [X2] : (r2_hidden(sK2(sK6(sK0)),sK6(sK0)) | r1_tarski(sK0,X2)) )),
% 0.21/0.55    inference(resolution,[],[f134,f62])).
% 0.21/0.55  fof(f134,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(sK2(X0),X0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f133,f86])).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    ( ! [X2] : (v3_ordinal1(sK2(X2)) | ~r2_hidden(X2,sK0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f42,f82])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ( ! [X2] : (~r2_hidden(X2,sK0) | v3_ordinal1(sK2(X2)) | ~v3_ordinal1(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f133,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(sK2(X0),X0) | ~v3_ordinal1(sK2(X0)) | ~r2_hidden(X0,sK0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f132,f82])).
% 0.21/0.55  fof(f132,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(sK2(X0),X0) | ~v3_ordinal1(sK2(X0)) | ~v3_ordinal1(X0) | ~r2_hidden(X0,sK0)) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f131])).
% 0.21/0.55  fof(f131,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(sK2(X0),X0) | ~v3_ordinal1(sK2(X0)) | ~v3_ordinal1(X0) | ~r2_hidden(X0,sK0) | ~v3_ordinal1(X0)) )),
% 0.21/0.55    inference(resolution,[],[f45,f44])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ( ! [X2] : (~r1_ordinal1(X2,sK2(X2)) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.55    inference(flattening,[],[f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),X0)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f31])).
% 0.21/0.55  % (24558)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),X0)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 0.21/0.55    inference(flattening,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).
% 0.21/0.55  fof(f375,plain,(
% 0.21/0.55    ( ! [X33,X32] : (r1_tarski(X32,k1_setfam_1(sK0)) | ~r2_hidden(sK4(sK0,X32),X33)) )),
% 0.21/0.55    inference(resolution,[],[f301,f58])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (24547)------------------------------
% 0.21/0.55  % (24547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (24547)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (24547)Memory used [KB]: 6524
% 0.21/0.55  % (24547)Time elapsed: 0.086 s
% 0.21/0.55  % (24547)------------------------------
% 0.21/0.55  % (24547)------------------------------
% 0.21/0.55  % (24561)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (24539)Success in time 0.187 s
%------------------------------------------------------------------------------
