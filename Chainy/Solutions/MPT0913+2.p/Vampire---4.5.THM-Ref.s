%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0913+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:57 EST 2020

% Result     : Theorem 2.56s
% Output     : Refutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 158 expanded)
%              Number of leaves         :    6 (  36 expanded)
%              Depth                    :   30
%              Number of atoms          :  155 ( 611 expanded)
%              Number of equality atoms :    4 (  24 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4009,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4008,f3946])).

fof(f3946,plain,(
    r2_hidden(sK82,sK85) ),
    inference(subsumption_resolution,[],[f3927,f2856])).

fof(f2856,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f2187])).

fof(f2187,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f2186])).

fof(f2186,plain,(
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

fof(f3927,plain,
    ( r2_hidden(sK82,sK85)
    | r2_hidden(k4_tarski(sK82,sK83),k2_zfmisc_1(sK85,sK86)) ),
    inference(resolution,[],[f3484,f2856])).

fof(f3484,plain,
    ( r2_hidden(k4_tarski(k4_tarski(sK82,sK83),sK84),k2_zfmisc_1(k2_zfmisc_1(sK85,sK86),sK87))
    | r2_hidden(sK82,sK85) ),
    inference(definition_unfolding,[],[f2442,f2507,f2500])).

fof(f2500,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1277])).

fof(f1277,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f2507,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1276])).

fof(f1276,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f2442,plain,
    ( r2_hidden(sK82,sK85)
    | r2_hidden(k3_mcart_1(sK82,sK83,sK84),k3_zfmisc_1(sK85,sK86,sK87)) ),
    inference(cnf_transformation,[],[f2008])).

fof(f2008,plain,
    ( ( ~ r2_hidden(sK84,sK87)
      | ~ r2_hidden(sK83,sK86)
      | ~ r2_hidden(sK82,sK85)
      | ~ r2_hidden(k3_mcart_1(sK82,sK83,sK84),k3_zfmisc_1(sK85,sK86,sK87)) )
    & ( ( r2_hidden(sK84,sK87)
        & r2_hidden(sK83,sK86)
        & r2_hidden(sK82,sK85) )
      | r2_hidden(k3_mcart_1(sK82,sK83,sK84),k3_zfmisc_1(sK85,sK86,sK87)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK82,sK83,sK84,sK85,sK86,sK87])],[f2006,f2007])).

fof(f2007,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ( ~ r2_hidden(X2,X5)
          | ~ r2_hidden(X1,X4)
          | ~ r2_hidden(X0,X3)
          | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) )
        & ( ( r2_hidden(X2,X5)
            & r2_hidden(X1,X4)
            & r2_hidden(X0,X3) )
          | r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) )
   => ( ( ~ r2_hidden(sK84,sK87)
        | ~ r2_hidden(sK83,sK86)
        | ~ r2_hidden(sK82,sK85)
        | ~ r2_hidden(k3_mcart_1(sK82,sK83,sK84),k3_zfmisc_1(sK85,sK86,sK87)) )
      & ( ( r2_hidden(sK84,sK87)
          & r2_hidden(sK83,sK86)
          & r2_hidden(sK82,sK85) )
        | r2_hidden(k3_mcart_1(sK82,sK83,sK84),k3_zfmisc_1(sK85,sK86,sK87)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2006,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( ~ r2_hidden(X2,X5)
        | ~ r2_hidden(X1,X4)
        | ~ r2_hidden(X0,X3)
        | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) )
      & ( ( r2_hidden(X2,X5)
          & r2_hidden(X1,X4)
          & r2_hidden(X0,X3) )
        | r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ) ),
    inference(flattening,[],[f2005])).

fof(f2005,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( ~ r2_hidden(X2,X5)
        | ~ r2_hidden(X1,X4)
        | ~ r2_hidden(X0,X3)
        | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) )
      & ( ( r2_hidden(X2,X5)
          & r2_hidden(X1,X4)
          & r2_hidden(X0,X3) )
        | r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ) ),
    inference(nnf_transformation,[],[f1392])).

fof(f1392,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
    <~> ( r2_hidden(X2,X5)
        & r2_hidden(X1,X4)
        & r2_hidden(X0,X3) ) ) ),
    inference(ennf_transformation,[],[f1382])).

fof(f1382,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
      <=> ( r2_hidden(X2,X5)
          & r2_hidden(X1,X4)
          & r2_hidden(X0,X3) ) ) ),
    inference(negated_conjecture,[],[f1381])).

fof(f1381,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
    <=> ( r2_hidden(X2,X5)
        & r2_hidden(X1,X4)
        & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_mcart_1)).

fof(f4008,plain,(
    ~ r2_hidden(sK82,sK85) ),
    inference(subsumption_resolution,[],[f4002,f3901])).

fof(f3901,plain,(
    r2_hidden(sK83,sK86) ),
    inference(subsumption_resolution,[],[f3882,f2857])).

fof(f2857,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f2187])).

fof(f3882,plain,
    ( r2_hidden(sK83,sK86)
    | r2_hidden(k4_tarski(sK82,sK83),k2_zfmisc_1(sK85,sK86)) ),
    inference(resolution,[],[f3483,f2856])).

fof(f3483,plain,
    ( r2_hidden(k4_tarski(k4_tarski(sK82,sK83),sK84),k2_zfmisc_1(k2_zfmisc_1(sK85,sK86),sK87))
    | r2_hidden(sK83,sK86) ),
    inference(definition_unfolding,[],[f2443,f2507,f2500])).

fof(f2443,plain,
    ( r2_hidden(sK83,sK86)
    | r2_hidden(k3_mcart_1(sK82,sK83,sK84),k3_zfmisc_1(sK85,sK86,sK87)) ),
    inference(cnf_transformation,[],[f2008])).

fof(f4002,plain,
    ( ~ r2_hidden(sK83,sK86)
    | ~ r2_hidden(sK82,sK85) ),
    inference(resolution,[],[f3977,f2858])).

fof(f2858,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f2187])).

fof(f3977,plain,(
    ~ r2_hidden(k4_tarski(sK82,sK83),k2_zfmisc_1(sK85,sK86)) ),
    inference(subsumption_resolution,[],[f3970,f3874])).

fof(f3874,plain,(
    r2_hidden(sK84,sK87) ),
    inference(subsumption_resolution,[],[f3482,f2857])).

fof(f3482,plain,
    ( r2_hidden(sK84,sK87)
    | r2_hidden(k4_tarski(k4_tarski(sK82,sK83),sK84),k2_zfmisc_1(k2_zfmisc_1(sK85,sK86),sK87)) ),
    inference(definition_unfolding,[],[f2444,f2507,f2500])).

fof(f2444,plain,
    ( r2_hidden(sK84,sK87)
    | r2_hidden(k3_mcart_1(sK82,sK83,sK84),k3_zfmisc_1(sK85,sK86,sK87)) ),
    inference(cnf_transformation,[],[f2008])).

fof(f3970,plain,
    ( ~ r2_hidden(sK84,sK87)
    | ~ r2_hidden(k4_tarski(sK82,sK83),k2_zfmisc_1(sK85,sK86)) ),
    inference(resolution,[],[f3966,f2858])).

fof(f3966,plain,(
    ~ r2_hidden(k4_tarski(k4_tarski(sK82,sK83),sK84),k2_zfmisc_1(k2_zfmisc_1(sK85,sK86),sK87)) ),
    inference(global_subsumption,[],[f3964,f3965])).

fof(f3965,plain,
    ( ~ r2_hidden(sK82,sK85)
    | ~ r2_hidden(k4_tarski(k4_tarski(sK82,sK83),sK84),k2_zfmisc_1(k2_zfmisc_1(sK85,sK86),sK87)) ),
    inference(subsumption_resolution,[],[f3873,f3901])).

fof(f3873,plain,
    ( ~ r2_hidden(sK83,sK86)
    | ~ r2_hidden(sK82,sK85)
    | ~ r2_hidden(k4_tarski(k4_tarski(sK82,sK83),sK84),k2_zfmisc_1(k2_zfmisc_1(sK85,sK86),sK87)) ),
    inference(subsumption_resolution,[],[f3481,f2854])).

fof(f2854,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f2185])).

fof(f2185,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f2184])).

fof(f2184,plain,(
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

fof(f3481,plain,
    ( ~ r2_hidden(sK84,sK87)
    | ~ r2_hidden(sK83,sK86)
    | ~ r2_hidden(sK82,sK85)
    | ~ r2_hidden(k4_tarski(k4_tarski(sK82,sK83),sK84),k2_zfmisc_1(k2_zfmisc_1(sK85,sK86),sK87)) ),
    inference(definition_unfolding,[],[f2445,f2507,f2500])).

fof(f2445,plain,
    ( ~ r2_hidden(sK84,sK87)
    | ~ r2_hidden(sK83,sK86)
    | ~ r2_hidden(sK82,sK85)
    | ~ r2_hidden(k3_mcart_1(sK82,sK83,sK84),k3_zfmisc_1(sK85,sK86,sK87)) ),
    inference(cnf_transformation,[],[f2008])).

fof(f3964,plain,(
    r2_hidden(sK82,sK85) ),
    inference(global_subsumption,[],[f3963])).

fof(f3963,plain,(
    r2_hidden(sK82,sK85) ),
    inference(global_subsumption,[],[f3962])).

fof(f3962,plain,(
    r2_hidden(sK82,sK85) ),
    inference(global_subsumption,[],[f3961])).

fof(f3961,plain,(
    r2_hidden(sK82,sK85) ),
    inference(global_subsumption,[],[f3960])).

fof(f3960,plain,(
    r2_hidden(sK82,sK85) ),
    inference(global_subsumption,[],[f3959])).

fof(f3959,plain,(
    r2_hidden(sK82,sK85) ),
    inference(global_subsumption,[],[f3958])).

fof(f3958,plain,(
    r2_hidden(sK82,sK85) ),
    inference(global_subsumption,[],[f3957])).

fof(f3957,plain,(
    r2_hidden(sK82,sK85) ),
    inference(global_subsumption,[],[f3956])).

fof(f3956,plain,(
    r2_hidden(sK82,sK85) ),
    inference(global_subsumption,[],[f3955])).

fof(f3955,plain,(
    r2_hidden(sK82,sK85) ),
    inference(global_subsumption,[],[f3954])).

fof(f3954,plain,(
    r2_hidden(sK82,sK85) ),
    inference(global_subsumption,[],[f3952])).

fof(f3952,plain,(
    r2_hidden(sK82,sK85) ),
    inference(global_subsumption,[],[f3950])).

fof(f3950,plain,(
    r2_hidden(sK82,sK85) ),
    inference(global_subsumption,[],[f3949])).

fof(f3949,plain,(
    r2_hidden(sK82,sK85) ),
    inference(global_subsumption,[],[f3948])).

fof(f3948,plain,(
    r2_hidden(sK82,sK85) ),
    inference(global_subsumption,[],[f3947])).

fof(f3947,plain,(
    r2_hidden(sK82,sK85) ),
    inference(subsumption_resolution,[],[f3929,f2856])).

fof(f3929,plain,
    ( r2_hidden(sK82,sK85)
    | r2_hidden(k4_tarski(sK82,sK83),k2_zfmisc_1(sK85,sK86)) ),
    inference(resolution,[],[f3484,f2853])).

fof(f2853,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f2185])).
%------------------------------------------------------------------------------
