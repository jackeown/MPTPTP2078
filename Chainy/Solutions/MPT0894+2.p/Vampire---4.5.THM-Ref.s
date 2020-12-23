%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0894+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   12 (  12 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    6
%              Number of atoms          :   13 (  13 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1934,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1822])).

fof(f1822,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
    inference(definition_unfolding,[],[f1573,f1820,f1701])).

fof(f1701,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1275])).

fof(f1275,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f1820,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f1350])).

fof(f1350,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_mcart_1)).

fof(f1573,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) != k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f1472])).

fof(f1472,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) != k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f1360,f1471])).

fof(f1471,plain,
    ( ? [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) != k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3)
   => k4_zfmisc_1(sK0,sK1,sK2,sK3) != k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f1360,plain,(
    ? [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) != k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ),
    inference(ennf_transformation,[],[f1352])).

fof(f1352,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ),
    inference(negated_conjecture,[],[f1351])).

fof(f1351,conjecture,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_mcart_1)).
%------------------------------------------------------------------------------
