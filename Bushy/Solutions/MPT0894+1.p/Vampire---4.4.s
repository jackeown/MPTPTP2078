%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t54_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:10 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   20 (  25 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   25 (  31 expanded)
%              Number of equality atoms :   17 (  22 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f31,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f30])).

fof(f30,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f29])).

fof(f29,plain,
    ( $false
    | ~ spl4_1 ),
    inference(trivial_inequality_removal,[],[f27])).

fof(f27,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | ~ spl4_1 ),
    inference(superposition,[],[f20,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(forward_demodulation,[],[f22,f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(forward_demodulation,[],[f13,f12])).

fof(f12,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t54_mcart_1.p',d3_zfmisc_1)).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t54_mcart_1.p',t53_mcart_1)).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ),
    inference(superposition,[],[f12,f12])).

fof(f20,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3) != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f19])).

fof(f19,plain,
    ( spl4_1
  <=> k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3) != k4_zfmisc_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f21,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f11,f19])).

fof(f11,plain,(
    k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3) != k4_zfmisc_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3) != k4_zfmisc_1(sK0,sK1,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3] : k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) != k4_zfmisc_1(X0,X1,X2,X3)
   => k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3) != k4_zfmisc_1(sK0,sK1,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] : k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) != k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] : k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t54_mcart_1.p',t54_mcart_1)).
%------------------------------------------------------------------------------
