%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0795+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:49 EST 2020

% Result     : Theorem 10.79s
% Output     : Refutation 11.06s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 263 expanded)
%              Number of leaves         :    8 (  64 expanded)
%              Depth                    :   17
%              Number of atoms          :  337 ( 912 expanded)
%              Number of equality atoms :   67 ( 166 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23225,plain,(
    $false ),
    inference(subsumption_resolution,[],[f23223,f23224])).

fof(f23224,plain,(
    ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(duplicate_literal_removal,[],[f23221])).

fof(f23221,plain,
    ( ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(backward_demodulation,[],[f22948,f23102])).

fof(f23102,plain,(
    sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))) = k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))) ),
    inference(resolution,[],[f4707,f2052])).

fof(f2052,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    inference(cnf_transformation,[],[f1219])).

fof(f1219,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1011])).

fof(f1011,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_1)).

fof(f4707,plain,(
    r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f4706,f3893])).

fof(f3893,plain,(
    ! [X90,X91] :
      ( ~ r2_hidden(k4_tarski(X90,X91),sK0)
      | r2_hidden(X91,k3_relat_1(sK0)) ) ),
    inference(resolution,[],[f2019,f2101])).

fof(f2101,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f1253])).

fof(f1253,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1252])).

fof(f1252,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f833])).

fof(f833,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

fof(f2019,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f1199])).

fof(f1199,plain,(
    ? [X0] :
      ( ~ r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0)))
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1185])).

fof(f1185,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0))) ) ),
    inference(negated_conjecture,[],[f1184])).

fof(f1184,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_wellord1)).

fof(f4706,plain,
    ( r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f4705,f2089])).

fof(f2089,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1023])).

fof(f1023,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

fof(f4705,plain,
    ( ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f4704,f2078])).

fof(f2078,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f863])).

fof(f863,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f4704,plain,
    ( k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f4703,f2077])).

fof(f2077,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f863])).

fof(f4703,plain,
    ( k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f4702,f2083])).

fof(f2083,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f921])).

fof(f921,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f4702,plain,
    ( ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f4701,f2088])).

fof(f2088,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f668])).

fof(f668,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f4701,plain,
    ( ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f4683,f2019])).

fof(f4683,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(duplicate_literal_removal,[],[f4677])).

fof(f4677,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(resolution,[],[f2020,f2027])).

fof(f2027,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k3_relat_1(X0) != k1_relat_1(X2)
      | k2_relat_1(X2) != k3_relat_1(X1)
      | ~ v2_funct_1(X2)
      | r2_hidden(sK2(X0,X1,X2),k3_relat_1(X0))
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)
      | r3_wellord1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f1201])).

fof(f1201,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k2_relat_1(X2) = k3_relat_1(X1)
                  & k3_relat_1(X0) = k1_relat_1(X2) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1200])).

fof(f1200,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k2_relat_1(X2) = k3_relat_1(X1)
                  & k3_relat_1(X0) = k1_relat_1(X2) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1137])).

fof(f1137,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k2_relat_1(X2) = k3_relat_1(X1)
                  & k3_relat_1(X0) = k1_relat_1(X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_wellord1)).

fof(f2020,plain,(
    ~ r3_wellord1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))) ),
    inference(cnf_transformation,[],[f1199])).

fof(f22948,plain,
    ( ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(backward_demodulation,[],[f4693,f22828])).

fof(f22828,plain,(
    sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))) = k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))) ),
    inference(resolution,[],[f4700,f2052])).

fof(f4700,plain,(
    r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f4699,f3892])).

fof(f3892,plain,(
    ! [X88,X89] :
      ( ~ r2_hidden(k4_tarski(X88,X89),sK0)
      | r2_hidden(X88,k3_relat_1(sK0)) ) ),
    inference(resolution,[],[f2019,f2100])).

fof(f2100,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f1253])).

fof(f4699,plain,
    ( r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f4698,f2089])).

fof(f4698,plain,
    ( ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f4697,f2078])).

fof(f4697,plain,
    ( k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f4696,f2077])).

fof(f4696,plain,
    ( k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f4695,f2083])).

fof(f4695,plain,
    ( ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f4694,f2088])).

fof(f4694,plain,
    ( ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f4684,f2019])).

fof(f4684,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(duplicate_literal_removal,[],[f4676])).

fof(f4676,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(resolution,[],[f2020,f2026])).

fof(f2026,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k3_relat_1(X0) != k1_relat_1(X2)
      | k2_relat_1(X2) != k3_relat_1(X1)
      | ~ v2_funct_1(X2)
      | r2_hidden(sK1(X0,X1,X2),k3_relat_1(X0))
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)
      | r3_wellord1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f1201])).

fof(f4693,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f4692,f3893])).

fof(f4692,plain,
    ( ~ r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f4691,f3892])).

fof(f4691,plain,
    ( ~ r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f4690,f2089])).

fof(f4690,plain,
    ( ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f4689,f2078])).

fof(f4689,plain,
    ( k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f4688,f2077])).

fof(f4688,plain,
    ( k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f4687,f2083])).

fof(f4687,plain,
    ( ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f4686,f2088])).

fof(f4686,plain,
    ( ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f4685,f2019])).

fof(f4685,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(duplicate_literal_removal,[],[f4675])).

fof(f4675,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(resolution,[],[f2020,f2025])).

fof(f2025,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k3_relat_1(X0) != k1_relat_1(X2)
      | k2_relat_1(X2) != k3_relat_1(X1)
      | ~ v2_funct_1(X2)
      | ~ r2_hidden(sK1(X0,X1,X2),k3_relat_1(X0))
      | ~ r2_hidden(sK2(X0,X1,X2),k3_relat_1(X0))
      | ~ r2_hidden(k4_tarski(k1_funct_1(X2,sK1(X0,X1,X2)),k1_funct_1(X2,sK2(X0,X1,X2))),X1)
      | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)
      | r3_wellord1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f1201])).

fof(f23223,plain,(
    r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(duplicate_literal_removal,[],[f23222])).

fof(f23222,plain,
    ( r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(backward_demodulation,[],[f22947,f23102])).

fof(f22947,plain,
    ( r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(backward_demodulation,[],[f4713,f22828])).

fof(f4713,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f4712,f2089])).

fof(f4712,plain,
    ( ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f4711,f2078])).

fof(f4711,plain,
    ( k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f4710,f2077])).

fof(f4710,plain,
    ( k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f4709,f2083])).

fof(f4709,plain,
    ( ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f4708,f2088])).

fof(f4708,plain,
    ( ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f4682,f2019])).

fof(f4682,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(duplicate_literal_removal,[],[f4678])).

fof(f4678,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(resolution,[],[f2020,f2028])).

fof(f2028,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k3_relat_1(X0) != k1_relat_1(X2)
      | k2_relat_1(X2) != k3_relat_1(X1)
      | ~ v2_funct_1(X2)
      | r2_hidden(k4_tarski(k1_funct_1(X2,sK1(X0,X1,X2)),k1_funct_1(X2,sK2(X0,X1,X2))),X1)
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)
      | r3_wellord1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f1201])).
%------------------------------------------------------------------------------
