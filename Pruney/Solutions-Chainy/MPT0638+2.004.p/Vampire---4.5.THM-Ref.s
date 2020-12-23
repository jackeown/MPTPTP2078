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
% DateTime   : Thu Dec  3 12:52:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 238 expanded)
%              Number of leaves         :    5 (  41 expanded)
%              Depth                    :   14
%              Number of atoms          :  209 (1192 expanded)
%              Number of equality atoms :   62 ( 475 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f452,plain,(
    $false ),
    inference(subsumption_resolution,[],[f451,f86])).

fof(f86,plain,(
    sK6(k2_relat_1(sK0),sK1) != k1_funct_1(sK1,sK6(k2_relat_1(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f85,f48])).

fof(f48,plain,(
    sK1 != k6_relat_1(k2_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f18,f16])).

fof(f16,plain,(
    k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(X0,X1) = X0
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(X0,X1) = X0
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X0,X1) = X0
                & k2_relat_1(X0) = k1_relat_1(X1) )
             => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k2_relat_1(X0) = k1_relat_1(X1) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_1)).

fof(f18,plain,(
    sK1 != k6_relat_1(k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f85,plain,
    ( sK1 = k6_relat_1(k2_relat_1(sK0))
    | sK6(k2_relat_1(sK0),sK1) != k1_funct_1(sK1,sK6(k2_relat_1(sK0),sK1)) ),
    inference(forward_demodulation,[],[f84,f16])).

fof(f84,plain,
    ( sK6(k2_relat_1(sK0),sK1) != k1_funct_1(sK1,sK6(k2_relat_1(sK0),sK1))
    | sK1 = k6_relat_1(k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f83,f16])).

fof(f83,plain,
    ( sK6(k1_relat_1(sK1),sK1) != k1_funct_1(sK1,sK6(k1_relat_1(sK1),sK1))
    | sK1 = k6_relat_1(k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f73,f14])).

fof(f14,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f73,plain,
    ( ~ v1_relat_1(sK1)
    | sK6(k1_relat_1(sK1),sK1) != k1_funct_1(sK1,sK6(k1_relat_1(sK1),sK1))
    | sK1 = k6_relat_1(k1_relat_1(sK1)) ),
    inference(resolution,[],[f15,f43])).

fof(f43,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | sK6(k1_relat_1(X1),X1) != k1_funct_1(X1,sK6(k1_relat_1(X1),X1))
      | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | sK6(X0,X1) != k1_funct_1(X1,sK6(X0,X1))
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

% (7115)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f15,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f451,plain,(
    sK6(k2_relat_1(sK0),sK1) = k1_funct_1(sK1,sK6(k2_relat_1(sK0),sK1)) ),
    inference(forward_demodulation,[],[f440,f270])).

fof(f270,plain,(
    sK6(k2_relat_1(sK0),sK1) = k1_funct_1(sK0,sK8(sK0,sK6(k2_relat_1(sK0),sK1))) ),
    inference(resolution,[],[f179,f82])).

fof(f82,plain,(
    r2_hidden(sK6(k2_relat_1(sK0),sK1),k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f81,f48])).

fof(f81,plain,
    ( sK1 = k6_relat_1(k2_relat_1(sK0))
    | r2_hidden(sK6(k2_relat_1(sK0),sK1),k2_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f80,f16])).

fof(f80,plain,
    ( r2_hidden(sK6(k2_relat_1(sK0),sK1),k2_relat_1(sK0))
    | sK1 = k6_relat_1(k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f79,f16])).

fof(f79,plain,
    ( r2_hidden(sK6(k1_relat_1(sK1),sK1),k1_relat_1(sK1))
    | sK1 = k6_relat_1(k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f72,f14])).

fof(f72,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(sK6(k1_relat_1(sK1),sK1),k1_relat_1(sK1))
    | sK1 = k6_relat_1(k1_relat_1(sK1)) ),
    inference(resolution,[],[f15,f44])).

fof(f44,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | r2_hidden(sK6(k1_relat_1(X1),X1),k1_relat_1(X1))
      | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | r2_hidden(sK6(X0,X1),X0)
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f179,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relat_1(sK0))
      | k1_funct_1(sK0,sK8(sK0,X3)) = X3 ) ),
    inference(resolution,[],[f113,f45])).

fof(f45,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK8(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f113,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK0)
      | k1_funct_1(sK0,X2) = X3 ) ),
    inference(subsumption_resolution,[],[f108,f19])).

fof(f19,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f108,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(sK0)
      | k1_funct_1(sK0,X2) = X3
      | ~ r2_hidden(k4_tarski(X2,X3),sK0) ) ),
    inference(resolution,[],[f20,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f20,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f440,plain,(
    k1_funct_1(sK1,sK6(k2_relat_1(sK0),sK1)) = k1_funct_1(sK0,sK8(sK0,sK6(k2_relat_1(sK0),sK1))) ),
    inference(resolution,[],[f360,f113])).

fof(f360,plain,(
    r2_hidden(k4_tarski(sK8(sK0,sK6(k2_relat_1(sK0),sK1)),k1_funct_1(sK1,sK6(k2_relat_1(sK0),sK1))),sK0) ),
    inference(resolution,[],[f359,f227])).

fof(f227,plain,(
    r2_hidden(k4_tarski(sK6(k2_relat_1(sK0),sK1),k1_funct_1(sK1,sK6(k2_relat_1(sK0),sK1))),sK1) ),
    inference(resolution,[],[f78,f82])).

fof(f78,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k2_relat_1(sK0))
      | r2_hidden(k4_tarski(X4,k1_funct_1(sK1,X4)),sK1) ) ),
    inference(forward_demodulation,[],[f77,f16])).

fof(f77,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_relat_1(sK1))
      | r2_hidden(k4_tarski(X4,k1_funct_1(sK1,X4)),sK1) ) ),
    inference(subsumption_resolution,[],[f71,f14])).

fof(f71,plain,(
    ! [X4] :
      ( ~ v1_relat_1(sK1)
      | ~ r2_hidden(X4,k1_relat_1(sK1))
      | r2_hidden(k4_tarski(X4,k1_funct_1(sK1,X4)),sK1) ) ),
    inference(resolution,[],[f15,f47])).

fof(f47,plain,(
    ! [X2,X0] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | k1_funct_1(X2,X0) != X1
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f359,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(k4_tarski(X6,X7),sK1)
      | r2_hidden(k4_tarski(sK8(sK0,X6),X7),sK0) ) ),
    inference(subsumption_resolution,[],[f352,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | r2_hidden(X0,k2_relat_1(sK0)) ) ),
    inference(forward_demodulation,[],[f74,f16])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(sK1))
      | ~ r2_hidden(k4_tarski(X0,X1),sK1) ) ),
    inference(subsumption_resolution,[],[f69,f14])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | r2_hidden(X0,k1_relat_1(sK1))
      | ~ r2_hidden(k4_tarski(X0,X1),sK1) ) ),
    inference(resolution,[],[f15,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f352,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(k4_tarski(X6,X7),sK1)
      | r2_hidden(k4_tarski(sK8(sK0,X6),X7),sK0)
      | ~ r2_hidden(X6,k2_relat_1(sK0)) ) ),
    inference(resolution,[],[f139,f45])).

fof(f139,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X4),sK0)
      | ~ r2_hidden(k4_tarski(X4,X5),sK1)
      | r2_hidden(k4_tarski(X3,X5),sK0) ) ),
    inference(subsumption_resolution,[],[f138,f14])).

fof(f138,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_relat_1(sK1)
      | ~ r2_hidden(k4_tarski(X3,X4),sK0)
      | ~ r2_hidden(k4_tarski(X4,X5),sK1)
      | r2_hidden(k4_tarski(X3,X5),sK0) ) ),
    inference(subsumption_resolution,[],[f137,f19])).

fof(f137,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_relat_1(sK0)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(k4_tarski(X3,X4),sK0)
      | ~ r2_hidden(k4_tarski(X4,X5),sK1)
      | r2_hidden(k4_tarski(X3,X5),sK0) ) ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_relat_1(sK0)
      | ~ v1_relat_1(sK0)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(k4_tarski(X3,X4),sK0)
      | ~ r2_hidden(k4_tarski(X4,X5),sK1)
      | r2_hidden(k4_tarski(X3,X5),sK0) ) ),
    inference(superposition,[],[f38,f17])).

fof(f17,plain,(
    sK0 = k5_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f38,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X3,X5),X0)
      | ~ r2_hidden(k4_tarski(X5,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X3,X5),X0)
      | ~ r2_hidden(k4_tarski(X5,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:55:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (7101)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (7110)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.50  % (7102)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (7107)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.51  % (7100)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (7109)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (7103)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.53  % (7110)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f452,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(subsumption_resolution,[],[f451,f86])).
% 0.20/0.53  fof(f86,plain,(
% 0.20/0.53    sK6(k2_relat_1(sK0),sK1) != k1_funct_1(sK1,sK6(k2_relat_1(sK0),sK1))),
% 0.20/0.53    inference(subsumption_resolution,[],[f85,f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    sK1 != k6_relat_1(k2_relat_1(sK0))),
% 0.20/0.53    inference(backward_demodulation,[],[f18,f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    k2_relat_1(sK0) = k1_relat_1(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.53    inference(flattening,[],[f7])).
% 0.20/0.53  fof(f7,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((k6_relat_1(k1_relat_1(X1)) != X1 & (k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,negated_conjecture,(
% 0.20/0.53    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 0.20/0.53    inference(negated_conjecture,[],[f5])).
% 0.20/0.53  fof(f5,conjecture,(
% 0.20/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_1)).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    sK1 != k6_relat_1(k1_relat_1(sK1))),
% 0.20/0.53    inference(cnf_transformation,[],[f8])).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    sK1 = k6_relat_1(k2_relat_1(sK0)) | sK6(k2_relat_1(sK0),sK1) != k1_funct_1(sK1,sK6(k2_relat_1(sK0),sK1))),
% 0.20/0.53    inference(forward_demodulation,[],[f84,f16])).
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    sK6(k2_relat_1(sK0),sK1) != k1_funct_1(sK1,sK6(k2_relat_1(sK0),sK1)) | sK1 = k6_relat_1(k1_relat_1(sK1))),
% 0.20/0.53    inference(forward_demodulation,[],[f83,f16])).
% 0.20/0.53  fof(f83,plain,(
% 0.20/0.53    sK6(k1_relat_1(sK1),sK1) != k1_funct_1(sK1,sK6(k1_relat_1(sK1),sK1)) | sK1 = k6_relat_1(k1_relat_1(sK1))),
% 0.20/0.53    inference(subsumption_resolution,[],[f73,f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    v1_relat_1(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f8])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    ~v1_relat_1(sK1) | sK6(k1_relat_1(sK1),sK1) != k1_funct_1(sK1,sK6(k1_relat_1(sK1),sK1)) | sK1 = k6_relat_1(k1_relat_1(sK1))),
% 0.20/0.53    inference(resolution,[],[f15,f43])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ( ! [X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | sK6(k1_relat_1(X1),X1) != k1_funct_1(X1,sK6(k1_relat_1(X1),X1)) | k6_relat_1(k1_relat_1(X1)) = X1) )),
% 0.20/0.53    inference(equality_resolution,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | sK6(X0,X1) != k1_funct_1(X1,sK6(X0,X1)) | k6_relat_1(X0) = X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,plain,(
% 0.20/0.53    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(flattening,[],[f10])).
% 0.20/0.53  fof(f10,plain,(
% 0.20/0.53    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).
% 0.20/0.53  % (7115)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    v1_funct_1(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f8])).
% 0.20/0.53  fof(f451,plain,(
% 0.20/0.53    sK6(k2_relat_1(sK0),sK1) = k1_funct_1(sK1,sK6(k2_relat_1(sK0),sK1))),
% 0.20/0.53    inference(forward_demodulation,[],[f440,f270])).
% 0.20/0.53  fof(f270,plain,(
% 0.20/0.53    sK6(k2_relat_1(sK0),sK1) = k1_funct_1(sK0,sK8(sK0,sK6(k2_relat_1(sK0),sK1)))),
% 0.20/0.53    inference(resolution,[],[f179,f82])).
% 0.20/0.53  fof(f82,plain,(
% 0.20/0.53    r2_hidden(sK6(k2_relat_1(sK0),sK1),k2_relat_1(sK0))),
% 0.20/0.53    inference(subsumption_resolution,[],[f81,f48])).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    sK1 = k6_relat_1(k2_relat_1(sK0)) | r2_hidden(sK6(k2_relat_1(sK0),sK1),k2_relat_1(sK0))),
% 0.20/0.53    inference(forward_demodulation,[],[f80,f16])).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    r2_hidden(sK6(k2_relat_1(sK0),sK1),k2_relat_1(sK0)) | sK1 = k6_relat_1(k1_relat_1(sK1))),
% 0.20/0.53    inference(forward_demodulation,[],[f79,f16])).
% 0.20/0.53  fof(f79,plain,(
% 0.20/0.53    r2_hidden(sK6(k1_relat_1(sK1),sK1),k1_relat_1(sK1)) | sK1 = k6_relat_1(k1_relat_1(sK1))),
% 0.20/0.53    inference(subsumption_resolution,[],[f72,f14])).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    ~v1_relat_1(sK1) | r2_hidden(sK6(k1_relat_1(sK1),sK1),k1_relat_1(sK1)) | sK1 = k6_relat_1(k1_relat_1(sK1))),
% 0.20/0.53    inference(resolution,[],[f15,f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ( ! [X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | r2_hidden(sK6(k1_relat_1(X1),X1),k1_relat_1(X1)) | k6_relat_1(k1_relat_1(X1)) = X1) )),
% 0.20/0.53    inference(equality_resolution,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | r2_hidden(sK6(X0,X1),X0) | k6_relat_1(X0) = X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f11])).
% 0.20/0.53  fof(f179,plain,(
% 0.20/0.53    ( ! [X3] : (~r2_hidden(X3,k2_relat_1(sK0)) | k1_funct_1(sK0,sK8(sK0,X3)) = X3) )),
% 0.20/0.53    inference(resolution,[],[f113,f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK8(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.20/0.53    inference(equality_resolution,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK8(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.20/0.53  fof(f113,plain,(
% 0.20/0.53    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK0) | k1_funct_1(sK0,X2) = X3) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f108,f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    v1_relat_1(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f8])).
% 0.20/0.53  fof(f108,plain,(
% 0.20/0.53    ( ! [X2,X3] : (~v1_relat_1(sK0) | k1_funct_1(sK0,X2) = X3 | ~r2_hidden(k4_tarski(X2,X3),sK0)) )),
% 0.20/0.53    inference(resolution,[],[f20,f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(flattening,[],[f12])).
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    v1_funct_1(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f8])).
% 0.20/0.53  fof(f440,plain,(
% 0.20/0.53    k1_funct_1(sK1,sK6(k2_relat_1(sK0),sK1)) = k1_funct_1(sK0,sK8(sK0,sK6(k2_relat_1(sK0),sK1)))),
% 0.20/0.53    inference(resolution,[],[f360,f113])).
% 0.20/0.53  fof(f360,plain,(
% 0.20/0.53    r2_hidden(k4_tarski(sK8(sK0,sK6(k2_relat_1(sK0),sK1)),k1_funct_1(sK1,sK6(k2_relat_1(sK0),sK1))),sK0)),
% 0.20/0.53    inference(resolution,[],[f359,f227])).
% 0.20/0.53  fof(f227,plain,(
% 0.20/0.53    r2_hidden(k4_tarski(sK6(k2_relat_1(sK0),sK1),k1_funct_1(sK1,sK6(k2_relat_1(sK0),sK1))),sK1)),
% 0.20/0.53    inference(resolution,[],[f78,f82])).
% 0.20/0.53  fof(f78,plain,(
% 0.20/0.53    ( ! [X4] : (~r2_hidden(X4,k2_relat_1(sK0)) | r2_hidden(k4_tarski(X4,k1_funct_1(sK1,X4)),sK1)) )),
% 0.20/0.53    inference(forward_demodulation,[],[f77,f16])).
% 0.20/0.53  fof(f77,plain,(
% 0.20/0.53    ( ! [X4] : (~r2_hidden(X4,k1_relat_1(sK1)) | r2_hidden(k4_tarski(X4,k1_funct_1(sK1,X4)),sK1)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f71,f14])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    ( ! [X4] : (~v1_relat_1(sK1) | ~r2_hidden(X4,k1_relat_1(sK1)) | r2_hidden(k4_tarski(X4,k1_funct_1(sK1,X4)),sK1)) )),
% 0.20/0.53    inference(resolution,[],[f15,f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X2,X0] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)) )),
% 0.20/0.53    inference(equality_resolution,[],[f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | k1_funct_1(X2,X0) != X1 | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f359,plain,(
% 0.20/0.53    ( ! [X6,X7] : (~r2_hidden(k4_tarski(X6,X7),sK1) | r2_hidden(k4_tarski(sK8(sK0,X6),X7),sK0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f352,f75])).
% 0.20/0.53  fof(f75,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | r2_hidden(X0,k2_relat_1(sK0))) )),
% 0.20/0.53    inference(forward_demodulation,[],[f74,f16])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(k4_tarski(X0,X1),sK1)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f69,f14])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_relat_1(sK1) | r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(k4_tarski(X0,X1),sK1)) )),
% 0.20/0.53    inference(resolution,[],[f15,f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f352,plain,(
% 0.20/0.53    ( ! [X6,X7] : (~r2_hidden(k4_tarski(X6,X7),sK1) | r2_hidden(k4_tarski(sK8(sK0,X6),X7),sK0) | ~r2_hidden(X6,k2_relat_1(sK0))) )),
% 0.20/0.53    inference(resolution,[],[f139,f45])).
% 0.20/0.53  fof(f139,plain,(
% 0.20/0.53    ( ! [X4,X5,X3] : (~r2_hidden(k4_tarski(X3,X4),sK0) | ~r2_hidden(k4_tarski(X4,X5),sK1) | r2_hidden(k4_tarski(X3,X5),sK0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f138,f14])).
% 0.20/0.53  fof(f138,plain,(
% 0.20/0.53    ( ! [X4,X5,X3] : (~v1_relat_1(sK1) | ~r2_hidden(k4_tarski(X3,X4),sK0) | ~r2_hidden(k4_tarski(X4,X5),sK1) | r2_hidden(k4_tarski(X3,X5),sK0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f137,f19])).
% 0.20/0.53  fof(f137,plain,(
% 0.20/0.53    ( ! [X4,X5,X3] : (~v1_relat_1(sK0) | ~v1_relat_1(sK1) | ~r2_hidden(k4_tarski(X3,X4),sK0) | ~r2_hidden(k4_tarski(X4,X5),sK1) | r2_hidden(k4_tarski(X3,X5),sK0)) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f129])).
% 0.20/0.53  fof(f129,plain,(
% 0.20/0.53    ( ! [X4,X5,X3] : (~v1_relat_1(sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(sK1) | ~r2_hidden(k4_tarski(X3,X4),sK0) | ~r2_hidden(k4_tarski(X4,X5),sK1) | r2_hidden(k4_tarski(X3,X5),sK0)) )),
% 0.20/0.53    inference(superposition,[],[f38,f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    sK0 = k5_relat_1(sK0,sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f8])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ( ! [X4,X0,X5,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X3,X5),X0) | ~r2_hidden(k4_tarski(X5,X4),X1) | r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))) )),
% 0.20/0.53    inference(equality_resolution,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X3,X5),X0) | ~r2_hidden(k4_tarski(X5,X4),X1) | r2_hidden(k4_tarski(X3,X4),X2) | k5_relat_1(X0,X1) != X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (7110)------------------------------
% 0.20/0.53  % (7110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (7110)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (7110)Memory used [KB]: 1918
% 0.20/0.53  % (7110)Time elapsed: 0.099 s
% 0.20/0.53  % (7110)------------------------------
% 0.20/0.53  % (7110)------------------------------
% 0.20/0.54  % (7096)Success in time 0.175 s
%------------------------------------------------------------------------------
