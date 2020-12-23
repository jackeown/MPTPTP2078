%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0924+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:58 EST 2020

% Result     : Theorem 1.86s
% Output     : Refutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 226 expanded)
%              Number of leaves         :    9 (  58 expanded)
%              Depth                    :   35
%              Number of atoms          :  230 ( 901 expanded)
%              Number of equality atoms :    8 (  60 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3907,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3906,f3828])).

fof(f3828,plain,(
    r2_hidden(sK82,sK86) ),
    inference(subsumption_resolution,[],[f3802,f2745])).

fof(f2745,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f2160])).

fof(f2160,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f2159])).

fof(f2159,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f325])).

fof(f325,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f3802,plain,
    ( r2_hidden(sK82,sK86)
    | r2_hidden(k4_tarski(sK82,sK83),k2_zfmisc_1(sK86,sK87)) ),
    inference(resolution,[],[f3420,f3481])).

fof(f3481,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(k4_tarski(k4_tarski(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5))
      | r2_hidden(X0,X3) ) ),
    inference(definition_unfolding,[],[f2797,f2932,f2848])).

fof(f2848,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1277])).

fof(f1277,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f2932,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1276])).

fof(f1276,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f2797,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(X0,X3)
      | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ),
    inference(cnf_transformation,[],[f2182])).

fof(f2182,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
        | ~ r2_hidden(X2,X5)
        | ~ r2_hidden(X1,X4)
        | ~ r2_hidden(X0,X3) )
      & ( ( r2_hidden(X2,X5)
          & r2_hidden(X1,X4)
          & r2_hidden(X0,X3) )
        | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ) ),
    inference(flattening,[],[f2181])).

fof(f2181,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
        | ~ r2_hidden(X2,X5)
        | ~ r2_hidden(X1,X4)
        | ~ r2_hidden(X0,X3) )
      & ( ( r2_hidden(X2,X5)
          & r2_hidden(X1,X4)
          & r2_hidden(X0,X3) )
        | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ) ),
    inference(nnf_transformation,[],[f1381])).

fof(f1381,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
    <=> ( r2_hidden(X2,X5)
        & r2_hidden(X1,X4)
        & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_mcart_1)).

fof(f3420,plain,
    ( r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK82,sK83),sK84),sK85),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK86,sK87),sK88),sK89))
    | r2_hidden(sK82,sK86) ),
    inference(definition_unfolding,[],[f2447,f2515,f2506])).

fof(f2506,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f1359])).

fof(f1359,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_mcart_1)).

fof(f2515,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f1335])).

fof(f1335,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).

fof(f2447,plain,
    ( r2_hidden(sK82,sK86)
    | r2_hidden(k4_mcart_1(sK82,sK83,sK84,sK85),k4_zfmisc_1(sK86,sK87,sK88,sK89)) ),
    inference(cnf_transformation,[],[f2013])).

fof(f2013,plain,
    ( ( ~ r2_hidden(sK85,sK89)
      | ~ r2_hidden(sK84,sK88)
      | ~ r2_hidden(sK83,sK87)
      | ~ r2_hidden(sK82,sK86)
      | ~ r2_hidden(k4_mcart_1(sK82,sK83,sK84,sK85),k4_zfmisc_1(sK86,sK87,sK88,sK89)) )
    & ( ( r2_hidden(sK85,sK89)
        & r2_hidden(sK84,sK88)
        & r2_hidden(sK83,sK87)
        & r2_hidden(sK82,sK86) )
      | r2_hidden(k4_mcart_1(sK82,sK83,sK84,sK85),k4_zfmisc_1(sK86,sK87,sK88,sK89)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK82,sK83,sK84,sK85,sK86,sK87,sK88,sK89])],[f2011,f2012])).

fof(f2012,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( ~ r2_hidden(X3,X7)
          | ~ r2_hidden(X2,X6)
          | ~ r2_hidden(X1,X5)
          | ~ r2_hidden(X0,X4)
          | ~ r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) )
        & ( ( r2_hidden(X3,X7)
            & r2_hidden(X2,X6)
            & r2_hidden(X1,X5)
            & r2_hidden(X0,X4) )
          | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) ) )
   => ( ( ~ r2_hidden(sK85,sK89)
        | ~ r2_hidden(sK84,sK88)
        | ~ r2_hidden(sK83,sK87)
        | ~ r2_hidden(sK82,sK86)
        | ~ r2_hidden(k4_mcart_1(sK82,sK83,sK84,sK85),k4_zfmisc_1(sK86,sK87,sK88,sK89)) )
      & ( ( r2_hidden(sK85,sK89)
          & r2_hidden(sK84,sK88)
          & r2_hidden(sK83,sK87)
          & r2_hidden(sK82,sK86) )
        | r2_hidden(k4_mcart_1(sK82,sK83,sK84,sK85),k4_zfmisc_1(sK86,sK87,sK88,sK89)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2011,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( ~ r2_hidden(X3,X7)
        | ~ r2_hidden(X2,X6)
        | ~ r2_hidden(X1,X5)
        | ~ r2_hidden(X0,X4)
        | ~ r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) )
      & ( ( r2_hidden(X3,X7)
          & r2_hidden(X2,X6)
          & r2_hidden(X1,X5)
          & r2_hidden(X0,X4) )
        | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) ) ) ),
    inference(flattening,[],[f2010])).

fof(f2010,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( ~ r2_hidden(X3,X7)
        | ~ r2_hidden(X2,X6)
        | ~ r2_hidden(X1,X5)
        | ~ r2_hidden(X0,X4)
        | ~ r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) )
      & ( ( r2_hidden(X3,X7)
          & r2_hidden(X2,X6)
          & r2_hidden(X1,X5)
          & r2_hidden(X0,X4) )
        | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) ) ) ),
    inference(nnf_transformation,[],[f1403])).

fof(f1403,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
    <~> ( r2_hidden(X3,X7)
        & r2_hidden(X2,X6)
        & r2_hidden(X1,X5)
        & r2_hidden(X0,X4) ) ) ),
    inference(ennf_transformation,[],[f1394])).

fof(f1394,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
      <=> ( r2_hidden(X3,X7)
          & r2_hidden(X2,X6)
          & r2_hidden(X1,X5)
          & r2_hidden(X0,X4) ) ) ),
    inference(negated_conjecture,[],[f1393])).

fof(f1393,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
    <=> ( r2_hidden(X3,X7)
        & r2_hidden(X2,X6)
        & r2_hidden(X1,X5)
        & r2_hidden(X0,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_mcart_1)).

fof(f3906,plain,(
    ~ r2_hidden(sK82,sK86) ),
    inference(subsumption_resolution,[],[f3900,f3771])).

fof(f3771,plain,(
    r2_hidden(sK83,sK87) ),
    inference(subsumption_resolution,[],[f3745,f2746])).

fof(f2746,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f2160])).

fof(f3745,plain,
    ( r2_hidden(sK83,sK87)
    | r2_hidden(k4_tarski(sK82,sK83),k2_zfmisc_1(sK86,sK87)) ),
    inference(resolution,[],[f3419,f3481])).

fof(f3419,plain,
    ( r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK82,sK83),sK84),sK85),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK86,sK87),sK88),sK89))
    | r2_hidden(sK83,sK87) ),
    inference(definition_unfolding,[],[f2448,f2515,f2506])).

fof(f2448,plain,
    ( r2_hidden(sK83,sK87)
    | r2_hidden(k4_mcart_1(sK82,sK83,sK84,sK85),k4_zfmisc_1(sK86,sK87,sK88,sK89)) ),
    inference(cnf_transformation,[],[f2013])).

fof(f3900,plain,
    ( ~ r2_hidden(sK83,sK87)
    | ~ r2_hidden(sK82,sK86) ),
    inference(resolution,[],[f3869,f2747])).

fof(f2747,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f2160])).

fof(f3869,plain,(
    ~ r2_hidden(k4_tarski(sK82,sK83),k2_zfmisc_1(sK86,sK87)) ),
    inference(subsumption_resolution,[],[f3868,f3730])).

fof(f3730,plain,(
    r2_hidden(sK84,sK88) ),
    inference(subsumption_resolution,[],[f3418,f3480])).

fof(f3480,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(k4_tarski(k4_tarski(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5))
      | r2_hidden(X1,X4) ) ),
    inference(definition_unfolding,[],[f2798,f2932,f2848])).

fof(f2798,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(X1,X4)
      | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ),
    inference(cnf_transformation,[],[f2182])).

fof(f3418,plain,
    ( r2_hidden(sK84,sK88)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK82,sK83),sK84),sK85),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK86,sK87),sK88),sK89)) ),
    inference(definition_unfolding,[],[f2449,f2515,f2506])).

fof(f2449,plain,
    ( r2_hidden(sK84,sK88)
    | r2_hidden(k4_mcart_1(sK82,sK83,sK84,sK85),k4_zfmisc_1(sK86,sK87,sK88,sK89)) ),
    inference(cnf_transformation,[],[f2013])).

fof(f3868,plain,
    ( ~ r2_hidden(sK84,sK88)
    | ~ r2_hidden(k4_tarski(sK82,sK83),k2_zfmisc_1(sK86,sK87)) ),
    inference(subsumption_resolution,[],[f3856,f3729])).

fof(f3729,plain,(
    r2_hidden(sK85,sK89) ),
    inference(subsumption_resolution,[],[f3417,f3479])).

fof(f3479,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(k4_tarski(k4_tarski(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5))
      | r2_hidden(X2,X5) ) ),
    inference(definition_unfolding,[],[f2799,f2932,f2848])).

fof(f2799,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(X2,X5)
      | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ),
    inference(cnf_transformation,[],[f2182])).

fof(f3417,plain,
    ( r2_hidden(sK85,sK89)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK82,sK83),sK84),sK85),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK86,sK87),sK88),sK89)) ),
    inference(definition_unfolding,[],[f2450,f2515,f2506])).

fof(f2450,plain,
    ( r2_hidden(sK85,sK89)
    | r2_hidden(k4_mcart_1(sK82,sK83,sK84,sK85),k4_zfmisc_1(sK86,sK87,sK88,sK89)) ),
    inference(cnf_transformation,[],[f2013])).

fof(f3856,plain,
    ( ~ r2_hidden(sK85,sK89)
    | ~ r2_hidden(sK84,sK88)
    | ~ r2_hidden(k4_tarski(sK82,sK83),k2_zfmisc_1(sK86,sK87)) ),
    inference(resolution,[],[f3853,f3478])).

fof(f3478,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(k4_tarski(k4_tarski(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5))
      | ~ r2_hidden(X2,X5)
      | ~ r2_hidden(X1,X4)
      | ~ r2_hidden(X0,X3) ) ),
    inference(definition_unfolding,[],[f2800,f2932,f2848])).

fof(f2800,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
      | ~ r2_hidden(X2,X5)
      | ~ r2_hidden(X1,X4)
      | ~ r2_hidden(X0,X3) ) ),
    inference(cnf_transformation,[],[f2182])).

fof(f3853,plain,(
    ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK82,sK83),sK84),sK85),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK86,sK87),sK88),sK89)) ),
    inference(global_subsumption,[],[f3851,f3852])).

fof(f3852,plain,
    ( ~ r2_hidden(sK82,sK86)
    | ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK82,sK83),sK84),sK85),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK86,sK87),sK88),sK89)) ),
    inference(subsumption_resolution,[],[f3728,f3771])).

fof(f3728,plain,
    ( ~ r2_hidden(sK83,sK87)
    | ~ r2_hidden(sK82,sK86)
    | ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK82,sK83),sK84),sK85),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK86,sK87),sK88),sK89)) ),
    inference(subsumption_resolution,[],[f3727,f3480])).

fof(f3727,plain,
    ( ~ r2_hidden(sK84,sK88)
    | ~ r2_hidden(sK83,sK87)
    | ~ r2_hidden(sK82,sK86)
    | ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK82,sK83),sK84),sK85),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK86,sK87),sK88),sK89)) ),
    inference(subsumption_resolution,[],[f3416,f2743])).

fof(f2743,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f2158])).

fof(f2158,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f2157])).

fof(f2157,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f318])).

fof(f318,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f3416,plain,
    ( ~ r2_hidden(sK85,sK89)
    | ~ r2_hidden(sK84,sK88)
    | ~ r2_hidden(sK83,sK87)
    | ~ r2_hidden(sK82,sK86)
    | ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK82,sK83),sK84),sK85),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK86,sK87),sK88),sK89)) ),
    inference(definition_unfolding,[],[f2451,f2515,f2506])).

fof(f2451,plain,
    ( ~ r2_hidden(sK85,sK89)
    | ~ r2_hidden(sK84,sK88)
    | ~ r2_hidden(sK83,sK87)
    | ~ r2_hidden(sK82,sK86)
    | ~ r2_hidden(k4_mcart_1(sK82,sK83,sK84,sK85),k4_zfmisc_1(sK86,sK87,sK88,sK89)) ),
    inference(cnf_transformation,[],[f2013])).

fof(f3851,plain,(
    r2_hidden(sK82,sK86) ),
    inference(global_subsumption,[],[f3850])).

fof(f3850,plain,(
    r2_hidden(sK82,sK86) ),
    inference(global_subsumption,[],[f3849])).

fof(f3849,plain,(
    r2_hidden(sK82,sK86) ),
    inference(global_subsumption,[],[f3848])).

fof(f3848,plain,(
    r2_hidden(sK82,sK86) ),
    inference(global_subsumption,[],[f3847])).

fof(f3847,plain,(
    r2_hidden(sK82,sK86) ),
    inference(global_subsumption,[],[f3846])).

fof(f3846,plain,(
    r2_hidden(sK82,sK86) ),
    inference(global_subsumption,[],[f3845])).

fof(f3845,plain,(
    r2_hidden(sK82,sK86) ),
    inference(global_subsumption,[],[f3844])).

fof(f3844,plain,(
    r2_hidden(sK82,sK86) ),
    inference(global_subsumption,[],[f3843])).

fof(f3843,plain,(
    r2_hidden(sK82,sK86) ),
    inference(global_subsumption,[],[f3842])).

fof(f3842,plain,(
    r2_hidden(sK82,sK86) ),
    inference(global_subsumption,[],[f3841])).

fof(f3841,plain,(
    r2_hidden(sK82,sK86) ),
    inference(global_subsumption,[],[f3840])).

fof(f3840,plain,(
    r2_hidden(sK82,sK86) ),
    inference(global_subsumption,[],[f3839])).

fof(f3839,plain,(
    r2_hidden(sK82,sK86) ),
    inference(global_subsumption,[],[f3838])).

fof(f3838,plain,(
    r2_hidden(sK82,sK86) ),
    inference(global_subsumption,[],[f3837])).

fof(f3837,plain,(
    r2_hidden(sK82,sK86) ),
    inference(global_subsumption,[],[f3835])).

fof(f3835,plain,(
    r2_hidden(sK82,sK86) ),
    inference(global_subsumption,[],[f3833])).

fof(f3833,plain,(
    r2_hidden(sK82,sK86) ),
    inference(global_subsumption,[],[f3832])).

fof(f3832,plain,(
    r2_hidden(sK82,sK86) ),
    inference(global_subsumption,[],[f3831])).

fof(f3831,plain,(
    r2_hidden(sK82,sK86) ),
    inference(global_subsumption,[],[f3830])).

fof(f3830,plain,(
    r2_hidden(sK82,sK86) ),
    inference(subsumption_resolution,[],[f3807,f3481])).

fof(f3807,plain,
    ( r2_hidden(sK82,sK86)
    | r2_hidden(k4_tarski(k4_tarski(sK82,sK83),sK84),k2_zfmisc_1(k2_zfmisc_1(sK86,sK87),sK88)) ),
    inference(resolution,[],[f3420,f2742])).

fof(f2742,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f2158])).
%------------------------------------------------------------------------------
