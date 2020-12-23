%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0659+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:43 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 259 expanded)
%              Number of leaves         :    8 (  82 expanded)
%              Depth                    :   37
%              Number of atoms          :  278 (1744 expanded)
%              Number of equality atoms :   29 ( 253 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3663,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3662,f2164])).

fof(f2164,plain,(
    v1_relat_1(sK100) ),
    inference(cnf_transformation,[],[f1701])).

% (20734)ott+11_8:1_av=off:bs=on:bce=on:fde=none:gsp=input_only:gs=on:gsem=on:irw=on:lcm=predicate:nm=6:nwc=1.5:sd=2:ss=axioms:st=1.2:sos=theory:urr=on:updr=off_49 on theBenchmark
fof(f1701,plain,
    ( k2_funct_1(k5_relat_1(sK100,sK101)) != k5_relat_1(k2_funct_1(sK101),k2_funct_1(sK100))
    & v2_funct_1(sK101)
    & v2_funct_1(sK100)
    & v1_funct_1(sK101)
    & v1_relat_1(sK101)
    & v1_funct_1(sK100)
    & v1_relat_1(sK100) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK100,sK101])],[f972,f1700,f1699])).

fof(f1699,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_funct_1(k5_relat_1(X0,X1)) != k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
            & v2_funct_1(X1)
            & v2_funct_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_funct_1(k5_relat_1(sK100,X1)) != k5_relat_1(k2_funct_1(X1),k2_funct_1(sK100))
          & v2_funct_1(X1)
          & v2_funct_1(sK100)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK100)
      & v1_relat_1(sK100) ) ),
    introduced(choice_axiom,[])).

fof(f1700,plain,
    ( ? [X1] :
        ( k2_funct_1(k5_relat_1(sK100,X1)) != k5_relat_1(k2_funct_1(X1),k2_funct_1(sK100))
        & v2_funct_1(X1)
        & v2_funct_1(sK100)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_funct_1(k5_relat_1(sK100,sK101)) != k5_relat_1(k2_funct_1(sK101),k2_funct_1(sK100))
      & v2_funct_1(sK101)
      & v2_funct_1(sK100)
      & v1_funct_1(sK101)
      & v1_relat_1(sK101) ) ),
    introduced(choice_axiom,[])).

fof(f972,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) != k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          & v2_funct_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f971])).

fof(f971,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) != k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          & v2_funct_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f962])).

fof(f962,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( v2_funct_1(X1)
                & v2_funct_1(X0) )
             => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f961])).

fof(f961,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_1)).

fof(f3662,plain,(
    ~ v1_relat_1(sK100) ),
    inference(subsumption_resolution,[],[f3661,f2165])).

fof(f2165,plain,(
    v1_funct_1(sK100) ),
    inference(cnf_transformation,[],[f1701])).

fof(f3661,plain,
    ( ~ v1_funct_1(sK100)
    | ~ v1_relat_1(sK100) ),
    inference(subsumption_resolution,[],[f3660,f2168])).

fof(f2168,plain,(
    v2_funct_1(sK100) ),
    inference(cnf_transformation,[],[f1701])).

fof(f3660,plain,
    ( ~ v2_funct_1(sK100)
    | ~ v1_funct_1(sK100)
    | ~ v1_relat_1(sK100) ),
    inference(subsumption_resolution,[],[f3659,f2166])).

fof(f2166,plain,(
    v1_relat_1(sK101) ),
    inference(cnf_transformation,[],[f1701])).

fof(f3659,plain,
    ( ~ v1_relat_1(sK101)
    | ~ v2_funct_1(sK100)
    | ~ v1_funct_1(sK100)
    | ~ v1_relat_1(sK100) ),
    inference(subsumption_resolution,[],[f3658,f2167])).

fof(f2167,plain,(
    v1_funct_1(sK101) ),
    inference(cnf_transformation,[],[f1701])).

fof(f3658,plain,
    ( ~ v1_funct_1(sK101)
    | ~ v1_relat_1(sK101)
    | ~ v2_funct_1(sK100)
    | ~ v1_funct_1(sK100)
    | ~ v1_relat_1(sK100) ),
    inference(subsumption_resolution,[],[f3651,f2169])).

fof(f2169,plain,(
    v2_funct_1(sK101) ),
    inference(cnf_transformation,[],[f1701])).

fof(f3651,plain,
    ( ~ v2_funct_1(sK101)
    | ~ v1_funct_1(sK101)
    | ~ v1_relat_1(sK101)
    | ~ v2_funct_1(sK100)
    | ~ v1_funct_1(sK100)
    | ~ v1_relat_1(sK100) ),
    inference(resolution,[],[f3649,f2269])).

fof(f2269,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1048])).

fof(f1048,plain,(
    ! [X0,X1] :
      ( ( v2_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1047])).

fof(f1047,plain,(
    ! [X0,X1] :
      ( ( v2_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f907])).

fof(f907,axiom,(
    ! [X0,X1] :
      ( ( v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1)
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_funct_1)).

% (20730)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f3649,plain,(
    ~ v1_relat_1(k5_relat_1(sK100,sK101)) ),
    inference(subsumption_resolution,[],[f3648,f2164])).

fof(f3648,plain,
    ( ~ v1_relat_1(k5_relat_1(sK100,sK101))
    | ~ v1_relat_1(sK100) ),
    inference(subsumption_resolution,[],[f3647,f2165])).

fof(f3647,plain,
    ( ~ v1_relat_1(k5_relat_1(sK100,sK101))
    | ~ v1_funct_1(sK100)
    | ~ v1_relat_1(sK100) ),
    inference(subsumption_resolution,[],[f3646,f2166])).

fof(f3646,plain,
    ( ~ v1_relat_1(k5_relat_1(sK100,sK101))
    | ~ v1_relat_1(sK101)
    | ~ v1_funct_1(sK100)
    | ~ v1_relat_1(sK100) ),
    inference(subsumption_resolution,[],[f3643,f2167])).

fof(f3643,plain,
    ( ~ v1_relat_1(k5_relat_1(sK100,sK101))
    | ~ v1_funct_1(sK101)
    | ~ v1_relat_1(sK101)
    | ~ v1_funct_1(sK100)
    | ~ v1_relat_1(sK100) ),
    inference(resolution,[],[f3618,f2230])).

fof(f2230,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1010])).

fof(f1010,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1009])).

fof(f1009,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f902])).

fof(f902,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f3618,plain,
    ( ~ v1_funct_1(k5_relat_1(sK100,sK101))
    | ~ v1_relat_1(k5_relat_1(sK100,sK101)) ),
    inference(subsumption_resolution,[],[f3617,f2164])).

fof(f3617,plain,
    ( ~ v1_funct_1(k5_relat_1(sK100,sK101))
    | ~ v1_relat_1(k5_relat_1(sK100,sK101))
    | ~ v1_relat_1(sK100) ),
    inference(subsumption_resolution,[],[f3616,f2165])).

fof(f3616,plain,
    ( ~ v1_funct_1(k5_relat_1(sK100,sK101))
    | ~ v1_relat_1(k5_relat_1(sK100,sK101))
    | ~ v1_funct_1(sK100)
    | ~ v1_relat_1(sK100) ),
    inference(subsumption_resolution,[],[f3615,f2166])).

fof(f3615,plain,
    ( ~ v1_funct_1(k5_relat_1(sK100,sK101))
    | ~ v1_relat_1(k5_relat_1(sK100,sK101))
    | ~ v1_relat_1(sK101)
    | ~ v1_funct_1(sK100)
    | ~ v1_relat_1(sK100) ),
    inference(subsumption_resolution,[],[f3614,f2167])).

fof(f3614,plain,
    ( ~ v1_funct_1(k5_relat_1(sK100,sK101))
    | ~ v1_relat_1(k5_relat_1(sK100,sK101))
    | ~ v1_funct_1(sK101)
    | ~ v1_relat_1(sK101)
    | ~ v1_funct_1(sK100)
    | ~ v1_relat_1(sK100) ),
    inference(subsumption_resolution,[],[f3613,f2168])).

fof(f3613,plain,
    ( ~ v1_funct_1(k5_relat_1(sK100,sK101))
    | ~ v1_relat_1(k5_relat_1(sK100,sK101))
    | ~ v2_funct_1(sK100)
    | ~ v1_funct_1(sK101)
    | ~ v1_relat_1(sK101)
    | ~ v1_funct_1(sK100)
    | ~ v1_relat_1(sK100) ),
    inference(subsumption_resolution,[],[f3610,f2169])).

fof(f3610,plain,
    ( ~ v1_funct_1(k5_relat_1(sK100,sK101))
    | ~ v1_relat_1(k5_relat_1(sK100,sK101))
    | ~ v2_funct_1(sK101)
    | ~ v2_funct_1(sK100)
    | ~ v1_funct_1(sK101)
    | ~ v1_relat_1(sK101)
    | ~ v1_funct_1(sK100)
    | ~ v1_relat_1(sK100) ),
    inference(resolution,[],[f3609,f2275])).

fof(f2275,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k5_relat_1(X0,X1))
      | ~ v2_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1056])).

fof(f1056,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1055])).

fof(f1055,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f941])).

fof(f941,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => v2_funct_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_funct_1)).

fof(f3609,plain,
    ( ~ v2_funct_1(k5_relat_1(sK100,sK101))
    | ~ v1_funct_1(k5_relat_1(sK100,sK101))
    | ~ v1_relat_1(k5_relat_1(sK100,sK101)) ),
    inference(trivial_inequality_removal,[],[f3607])).

fof(f3607,plain,
    ( k4_relat_1(k5_relat_1(sK100,sK101)) != k4_relat_1(k5_relat_1(sK100,sK101))
    | ~ v2_funct_1(k5_relat_1(sK100,sK101))
    | ~ v1_funct_1(k5_relat_1(sK100,sK101))
    | ~ v1_relat_1(k5_relat_1(sK100,sK101)) ),
    inference(superposition,[],[f3605,f2209])).

fof(f2209,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f996])).

fof(f996,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f995])).

fof(f995,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f894])).

fof(f894,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f3605,plain,(
    k2_funct_1(k5_relat_1(sK100,sK101)) != k4_relat_1(k5_relat_1(sK100,sK101)) ),
    inference(subsumption_resolution,[],[f3604,f2164])).

fof(f3604,plain,
    ( k2_funct_1(k5_relat_1(sK100,sK101)) != k4_relat_1(k5_relat_1(sK100,sK101))
    | ~ v1_relat_1(sK100) ),
    inference(subsumption_resolution,[],[f3602,f2166])).

fof(f3602,plain,
    ( k2_funct_1(k5_relat_1(sK100,sK101)) != k4_relat_1(k5_relat_1(sK100,sK101))
    | ~ v1_relat_1(sK101)
    | ~ v1_relat_1(sK100) ),
    inference(superposition,[],[f3592,f2505])).

fof(f2505,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1166])).

fof(f1166,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f853])).

fof(f853,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(f3592,plain,(
    k2_funct_1(k5_relat_1(sK100,sK101)) != k5_relat_1(k4_relat_1(sK101),k4_relat_1(sK100)) ),
    inference(subsumption_resolution,[],[f3591,f2164])).

fof(f3591,plain,
    ( k2_funct_1(k5_relat_1(sK100,sK101)) != k5_relat_1(k4_relat_1(sK101),k4_relat_1(sK100))
    | ~ v1_relat_1(sK100) ),
    inference(subsumption_resolution,[],[f3590,f2165])).

fof(f3590,plain,
    ( k2_funct_1(k5_relat_1(sK100,sK101)) != k5_relat_1(k4_relat_1(sK101),k4_relat_1(sK100))
    | ~ v1_funct_1(sK100)
    | ~ v1_relat_1(sK100) ),
    inference(subsumption_resolution,[],[f3587,f2168])).

fof(f3587,plain,
    ( k2_funct_1(k5_relat_1(sK100,sK101)) != k5_relat_1(k4_relat_1(sK101),k4_relat_1(sK100))
    | ~ v2_funct_1(sK100)
    | ~ v1_funct_1(sK100)
    | ~ v1_relat_1(sK100) ),
    inference(superposition,[],[f3582,f2209])).

fof(f3582,plain,(
    k2_funct_1(k5_relat_1(sK100,sK101)) != k5_relat_1(k4_relat_1(sK101),k2_funct_1(sK100)) ),
    inference(subsumption_resolution,[],[f3581,f2166])).

fof(f3581,plain,
    ( k2_funct_1(k5_relat_1(sK100,sK101)) != k5_relat_1(k4_relat_1(sK101),k2_funct_1(sK100))
    | ~ v1_relat_1(sK101) ),
    inference(subsumption_resolution,[],[f3580,f2167])).

fof(f3580,plain,
    ( k2_funct_1(k5_relat_1(sK100,sK101)) != k5_relat_1(k4_relat_1(sK101),k2_funct_1(sK100))
    | ~ v1_funct_1(sK101)
    | ~ v1_relat_1(sK101) ),
    inference(subsumption_resolution,[],[f3575,f2169])).

fof(f3575,plain,
    ( k2_funct_1(k5_relat_1(sK100,sK101)) != k5_relat_1(k4_relat_1(sK101),k2_funct_1(sK100))
    | ~ v2_funct_1(sK101)
    | ~ v1_funct_1(sK101)
    | ~ v1_relat_1(sK101) ),
    inference(superposition,[],[f2170,f2209])).

fof(f2170,plain,(
    k2_funct_1(k5_relat_1(sK100,sK101)) != k5_relat_1(k2_funct_1(sK101),k2_funct_1(sK100)) ),
    inference(cnf_transformation,[],[f1701])).
%------------------------------------------------------------------------------
