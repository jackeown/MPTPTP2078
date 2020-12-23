%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0646+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:42 EST 2020

% Result     : Theorem 1.84s
% Output     : Refutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 114 expanded)
%              Number of leaves         :    7 (  37 expanded)
%              Depth                    :   19
%              Number of atoms          :  155 ( 640 expanded)
%              Number of equality atoms :   18 ( 109 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3230,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3229,f1979])).

fof(f1979,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f939])).

fof(f939,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

fof(f3229,plain,(
    ~ v2_funct_1(k6_relat_1(k1_relat_1(sK80))) ),
    inference(forward_demodulation,[],[f3228,f1948])).

fof(f1948,plain,(
    k6_relat_1(k1_relat_1(sK80)) = k5_relat_1(sK80,sK81) ),
    inference(cnf_transformation,[],[f1541])).

fof(f1541,plain,
    ( ~ v2_funct_1(sK80)
    & k6_relat_1(k1_relat_1(sK80)) = k5_relat_1(sK80,sK81)
    & v1_funct_1(sK81)
    & v1_relat_1(sK81)
    & v1_funct_1(sK80)
    & v1_relat_1(sK80) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK80,sK81])],[f951,f1540,f1539])).

fof(f1539,plain,
    ( ? [X0] :
        ( ~ v2_funct_1(X0)
        & ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v2_funct_1(sK80)
      & ? [X1] :
          ( k5_relat_1(sK80,X1) = k6_relat_1(k1_relat_1(sK80))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK80)
      & v1_relat_1(sK80) ) ),
    introduced(choice_axiom,[])).

fof(f1540,plain,
    ( ? [X1] :
        ( k5_relat_1(sK80,X1) = k6_relat_1(k1_relat_1(sK80))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k6_relat_1(k1_relat_1(sK80)) = k5_relat_1(sK80,sK81)
      & v1_funct_1(sK81)
      & v1_relat_1(sK81) ) ),
    introduced(choice_axiom,[])).

fof(f951,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ? [X1] :
          ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f950])).

fof(f950,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ? [X1] :
          ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f941])).

fof(f941,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( ? [X1] :
              ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & v1_funct_1(X1)
              & v1_relat_1(X1) )
         => v2_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f940])).

fof(f940,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).

fof(f3228,plain,(
    ~ v2_funct_1(k5_relat_1(sK80,sK81)) ),
    inference(subsumption_resolution,[],[f3227,f1946])).

fof(f1946,plain,(
    v1_relat_1(sK81) ),
    inference(cnf_transformation,[],[f1541])).

fof(f3227,plain,
    ( ~ v2_funct_1(k5_relat_1(sK80,sK81))
    | ~ v1_relat_1(sK81) ),
    inference(subsumption_resolution,[],[f3226,f1947])).

fof(f1947,plain,(
    v1_funct_1(sK81) ),
    inference(cnf_transformation,[],[f1541])).

fof(f3226,plain,
    ( ~ v2_funct_1(k5_relat_1(sK80,sK81))
    | ~ v1_funct_1(sK81)
    | ~ v1_relat_1(sK81) ),
    inference(subsumption_resolution,[],[f3225,f1944])).

fof(f1944,plain,(
    v1_relat_1(sK80) ),
    inference(cnf_transformation,[],[f1541])).

fof(f3225,plain,
    ( ~ v2_funct_1(k5_relat_1(sK80,sK81))
    | ~ v1_relat_1(sK80)
    | ~ v1_funct_1(sK81)
    | ~ v1_relat_1(sK81) ),
    inference(subsumption_resolution,[],[f3224,f1945])).

fof(f1945,plain,(
    v1_funct_1(sK80) ),
    inference(cnf_transformation,[],[f1541])).

fof(f3224,plain,
    ( ~ v2_funct_1(k5_relat_1(sK80,sK81))
    | ~ v1_funct_1(sK80)
    | ~ v1_relat_1(sK80)
    | ~ v1_funct_1(sK81)
    | ~ v1_relat_1(sK81) ),
    inference(subsumption_resolution,[],[f3213,f1949])).

fof(f1949,plain,(
    ~ v2_funct_1(sK80) ),
    inference(cnf_transformation,[],[f1541])).

fof(f3213,plain,
    ( v2_funct_1(sK80)
    | ~ v2_funct_1(k5_relat_1(sK80,sK81))
    | ~ v1_funct_1(sK80)
    | ~ v1_relat_1(sK80)
    | ~ v1_funct_1(sK81)
    | ~ v1_relat_1(sK81) ),
    inference(resolution,[],[f3152,f1952])).

fof(f1952,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | v2_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f957])).

fof(f957,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f956])).

fof(f956,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f934])).

fof(f934,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => v2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).

fof(f3152,plain,(
    r1_tarski(k2_relat_1(sK80),k1_relat_1(sK81)) ),
    inference(subsumption_resolution,[],[f3151,f1946])).

fof(f3151,plain,
    ( r1_tarski(k2_relat_1(sK80),k1_relat_1(sK81))
    | ~ v1_relat_1(sK81) ),
    inference(subsumption_resolution,[],[f3150,f1947])).

fof(f3150,plain,
    ( r1_tarski(k2_relat_1(sK80),k1_relat_1(sK81))
    | ~ v1_funct_1(sK81)
    | ~ v1_relat_1(sK81) ),
    inference(subsumption_resolution,[],[f3149,f1944])).

fof(f3149,plain,
    ( r1_tarski(k2_relat_1(sK80),k1_relat_1(sK81))
    | ~ v1_relat_1(sK80)
    | ~ v1_funct_1(sK81)
    | ~ v1_relat_1(sK81) ),
    inference(subsumption_resolution,[],[f3148,f1945])).

fof(f3148,plain,
    ( r1_tarski(k2_relat_1(sK80),k1_relat_1(sK81))
    | ~ v1_funct_1(sK80)
    | ~ v1_relat_1(sK80)
    | ~ v1_funct_1(sK81)
    | ~ v1_relat_1(sK81) ),
    inference(subsumption_resolution,[],[f3098,f2031])).

fof(f2031,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f863])).

fof(f863,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f3098,plain,
    ( k1_relat_1(sK80) != k1_relat_1(k6_relat_1(k1_relat_1(sK80)))
    | r1_tarski(k2_relat_1(sK80),k1_relat_1(sK81))
    | ~ v1_funct_1(sK80)
    | ~ v1_relat_1(sK80)
    | ~ v1_funct_1(sK81)
    | ~ v1_relat_1(sK81) ),
    inference(superposition,[],[f2073,f1948])).

fof(f2073,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1026])).

fof(f1026,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1025])).

fof(f1025,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f924])).

fof(f924,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).
%------------------------------------------------------------------------------
