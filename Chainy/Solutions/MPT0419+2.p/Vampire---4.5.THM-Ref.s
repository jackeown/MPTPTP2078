%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0419+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:29 EST 2020

% Result     : Theorem 4.30s
% Output     : Refutation 4.30s
% Verified   : 
% Statistics : Number of formulae       :   41 (  98 expanded)
%              Number of leaves         :    7 (  28 expanded)
%              Depth                    :   16
%              Number of atoms          :  135 ( 391 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7007,plain,(
    $false ),
    inference(subsumption_resolution,[],[f7005,f1378])).

fof(f1378,plain,(
    ~ r1_tarski(sK11,sK12) ),
    inference(cnf_transformation,[],[f1038])).

fof(f1038,plain,
    ( ~ r1_tarski(sK11,sK12)
    & r1_tarski(k7_setfam_1(sK10,sK11),k7_setfam_1(sK10,sK12))
    & m1_subset_1(sK12,k1_zfmisc_1(k1_zfmisc_1(sK10)))
    & m1_subset_1(sK11,k1_zfmisc_1(k1_zfmisc_1(sK10))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f630,f1037,f1036])).

fof(f1036,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X1,X2)
            & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(sK11,X2)
          & r1_tarski(k7_setfam_1(sK10,sK11),k7_setfam_1(sK10,X2))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK10))) )
      & m1_subset_1(sK11,k1_zfmisc_1(k1_zfmisc_1(sK10))) ) ),
    introduced(choice_axiom,[])).

fof(f1037,plain,
    ( ? [X2] :
        ( ~ r1_tarski(sK11,X2)
        & r1_tarski(k7_setfam_1(sK10,sK11),k7_setfam_1(sK10,X2))
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK10))) )
   => ( ~ r1_tarski(sK11,sK12)
      & r1_tarski(k7_setfam_1(sK10,sK11),k7_setfam_1(sK10,sK12))
      & m1_subset_1(sK12,k1_zfmisc_1(k1_zfmisc_1(sK10))) ) ),
    introduced(choice_axiom,[])).

fof(f630,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f629])).

fof(f629,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f606])).

fof(f606,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
             => r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f605])).

fof(f605,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_setfam_1)).

fof(f7005,plain,(
    r1_tarski(sK11,sK12) ),
    inference(duplicate_literal_removal,[],[f6993])).

fof(f6993,plain,
    ( r1_tarski(sK11,sK12)
    | r1_tarski(sK11,sK12) ),
    inference(resolution,[],[f5842,f1756])).

fof(f1756,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK61(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1175])).

fof(f1175,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK61(X0,X1),X1)
          & r2_hidden(sK61(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK61])],[f1173,f1174])).

fof(f1174,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK61(X0,X1),X1)
        & r2_hidden(sK61(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1173,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1172])).

fof(f1172,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f820])).

fof(f820,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f5842,plain,(
    ! [X57] :
      ( r2_hidden(sK61(sK11,X57),sK12)
      | r1_tarski(sK11,X57) ) ),
    inference(resolution,[],[f5810,f1755])).

fof(f1755,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK61(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1175])).

fof(f5810,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK11)
      | r2_hidden(X0,sK12) ) ),
    inference(subsumption_resolution,[],[f5809,f3070])).

fof(f3070,plain,(
    ! [X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(sK10))
      | ~ r2_hidden(X1,sK11) ) ),
    inference(resolution,[],[f1375,f1931])).

fof(f1931,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f904])).

fof(f904,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f903])).

fof(f903,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f604])).

fof(f604,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f1375,plain,(
    m1_subset_1(sK11,k1_zfmisc_1(k1_zfmisc_1(sK10))) ),
    inference(cnf_transformation,[],[f1038])).

fof(f5809,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK11)
      | r2_hidden(X0,sK12)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK10)) ) ),
    inference(subsumption_resolution,[],[f5798,f1376])).

fof(f1376,plain,(
    m1_subset_1(sK12,k1_zfmisc_1(k1_zfmisc_1(sK10))) ),
    inference(cnf_transformation,[],[f1038])).

fof(f5798,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK11)
      | r2_hidden(X0,sK12)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK10))
      | ~ m1_subset_1(sK12,k1_zfmisc_1(k1_zfmisc_1(sK10))) ) ),
    inference(resolution,[],[f3531,f1683])).

fof(f1683,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f1126])).

fof(f1126,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
              | ~ r2_hidden(X2,X1) )
            & ( r2_hidden(X2,X1)
              | ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f785])).

fof(f785,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f602])).

fof(f602,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_setfam_1)).

fof(f3531,plain,(
    ! [X17] :
      ( r2_hidden(k3_subset_1(sK10,X17),k7_setfam_1(sK10,sK12))
      | ~ r2_hidden(X17,sK11) ) ),
    inference(subsumption_resolution,[],[f3530,f3070])).

fof(f3530,plain,(
    ! [X17] :
      ( r2_hidden(k3_subset_1(sK10,X17),k7_setfam_1(sK10,sK12))
      | ~ r2_hidden(X17,sK11)
      | ~ m1_subset_1(X17,k1_zfmisc_1(sK10)) ) ),
    inference(subsumption_resolution,[],[f3474,f1375])).

fof(f3474,plain,(
    ! [X17] :
      ( r2_hidden(k3_subset_1(sK10,X17),k7_setfam_1(sK10,sK12))
      | ~ r2_hidden(X17,sK11)
      | ~ m1_subset_1(X17,k1_zfmisc_1(sK10))
      | ~ m1_subset_1(sK11,k1_zfmisc_1(k1_zfmisc_1(sK10))) ) ),
    inference(resolution,[],[f3134,f1684])).

fof(f1684,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f1126])).

fof(f3134,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k7_setfam_1(sK10,sK11))
      | r2_hidden(X0,k7_setfam_1(sK10,sK12)) ) ),
    inference(resolution,[],[f1377,f1754])).

fof(f1754,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f1175])).

fof(f1377,plain,(
    r1_tarski(k7_setfam_1(sK10,sK11),k7_setfam_1(sK10,sK12)) ),
    inference(cnf_transformation,[],[f1038])).
%------------------------------------------------------------------------------
