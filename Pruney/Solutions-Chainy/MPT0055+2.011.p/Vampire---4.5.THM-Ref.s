%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:05 EST 2020

% Result     : Theorem 5.52s
% Output     : Refutation 5.52s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 456 expanded)
%              Number of leaves         :    7 ( 111 expanded)
%              Depth                    :   17
%              Number of atoms          :  161 (3004 expanded)
%              Number of equality atoms :   30 ( 492 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1758,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1716,f1738])).

fof(f1738,plain,(
    ! [X1] : ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) ),
    inference(subsumption_resolution,[],[f1546,f1729])).

fof(f1729,plain,(
    ! [X0] : ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,sK0)) ),
    inference(superposition,[],[f1408,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f1408,plain,(
    ! [X8,X7] : ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X7,k2_xboole_0(X8,k3_xboole_0(sK0,sK1)))) ),
    inference(subsumption_resolution,[],[f453,f1397])).

fof(f1397,plain,(
    ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(global_subsumption,[],[f1076,f1384])).

fof(f1384,plain,(
    ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1375,f80])).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f1375,plain,
    ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1) ),
    inference(superposition,[],[f406,f53])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f406,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1)))
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1) ) ),
    inference(resolution,[],[f226,f80])).

fof(f226,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1) ),
    inference(subsumption_resolution,[],[f214,f116])).

fof(f116,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( k3_xboole_0(sK0,sK1) != X0
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X0),sK0)
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X0),X0) ) ),
    inference(superposition,[],[f42,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f42,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f29])).

fof(f29,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f214,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)
    | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(resolution,[],[f122,f79])).

fof(f79,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f122,plain,
    ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X1] :
      ( k3_xboole_0(sK0,sK1) != X1
      | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X1),k4_xboole_0(sK0,sK1))
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X1),X1) ) ),
    inference(superposition,[],[f42,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1076,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(duplicate_literal_removal,[],[f1070])).

fof(f1070,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(superposition,[],[f294,f53])).

fof(f294,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,k3_xboole_0(sK0,sK1)))
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
      | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
      | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) ) ),
    inference(resolution,[],[f134,f79])).

fof(f134,plain,
    ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X2] :
      ( k3_xboole_0(sK0,sK1) != X2
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X2),k4_xboole_0(sK0,sK1))
      | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X2),sK0)
      | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X2),X2) ) ),
    inference(superposition,[],[f42,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f453,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X7,k2_xboole_0(X8,k3_xboole_0(sK0,sK1))))
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ) ),
    inference(superposition,[],[f188,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f188,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1)))
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ) ),
    inference(resolution,[],[f116,f80])).

fof(f1546,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,sK0))
      | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) ) ),
    inference(resolution,[],[f1397,f79])).

fof(f1716,plain,(
    ! [X0] : r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(X0,k3_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f1408,f1400])).

fof(f1400,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),X1))
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) ) ),
    inference(subsumption_resolution,[],[f189,f1397])).

fof(f189,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),X1))
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) ) ),
    inference(resolution,[],[f116,f79])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n025.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 15:39:35 EST 2020
% 0.14/0.36  % CPUTime    : 
% 1.28/0.54  % (24496)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.28/0.54  % (24496)Refutation not found, incomplete strategy% (24496)------------------------------
% 1.28/0.54  % (24496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (24522)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.28/0.54  % (24496)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (24496)Memory used [KB]: 10618
% 1.28/0.54  % (24496)Time elapsed: 0.114 s
% 1.28/0.54  % (24496)------------------------------
% 1.28/0.54  % (24496)------------------------------
% 1.28/0.55  % (24497)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.28/0.55  % (24503)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.28/0.55  % (24498)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.28/0.55  % (24494)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.28/0.55  % (24494)Refutation not found, incomplete strategy% (24494)------------------------------
% 1.28/0.55  % (24494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.55  % (24494)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.55  
% 1.28/0.55  % (24494)Memory used [KB]: 1663
% 1.28/0.55  % (24494)Time elapsed: 0.120 s
% 1.28/0.55  % (24494)------------------------------
% 1.28/0.55  % (24494)------------------------------
% 1.28/0.55  % (24505)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.28/0.55  % (24498)Refutation not found, incomplete strategy% (24498)------------------------------
% 1.28/0.55  % (24498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.55  % (24498)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.55  
% 1.28/0.55  % (24498)Memory used [KB]: 6140
% 1.28/0.55  % (24498)Time elapsed: 0.121 s
% 1.28/0.55  % (24498)------------------------------
% 1.28/0.55  % (24498)------------------------------
% 1.28/0.55  % (24505)Refutation not found, incomplete strategy% (24505)------------------------------
% 1.28/0.55  % (24505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.55  % (24504)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.45/0.55  % (24509)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.45/0.55  % (24518)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.45/0.56  % (24508)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.45/0.56  % (24519)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.45/0.56  % (24505)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (24505)Memory used [KB]: 10618
% 1.45/0.56  % (24505)Time elapsed: 0.128 s
% 1.45/0.56  % (24505)------------------------------
% 1.45/0.56  % (24505)------------------------------
% 1.45/0.56  % (24524)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.45/0.56  % (24500)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.45/0.56  % (24523)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.45/0.56  % (24521)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.45/0.56  % (24518)Refutation not found, incomplete strategy% (24518)------------------------------
% 1.45/0.56  % (24518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (24511)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.45/0.56  % (24518)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (24518)Memory used [KB]: 10746
% 1.45/0.56  % (24518)Time elapsed: 0.070 s
% 1.45/0.56  % (24518)------------------------------
% 1.45/0.56  % (24518)------------------------------
% 1.45/0.56  % (24510)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.45/0.56  % (24516)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.45/0.56  % (24510)Refutation not found, incomplete strategy% (24510)------------------------------
% 1.45/0.56  % (24510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (24510)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (24510)Memory used [KB]: 6140
% 1.45/0.56  % (24510)Time elapsed: 0.146 s
% 1.45/0.56  % (24510)------------------------------
% 1.45/0.56  % (24510)------------------------------
% 1.45/0.56  % (24515)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.45/0.56  % (24514)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.45/0.57  % (24507)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.45/0.57  % (24495)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.45/0.57  % (24501)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.45/0.57  % (24502)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.45/0.57  % (24506)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.45/0.57  % (24525)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.45/0.57  % (24504)Refutation not found, incomplete strategy% (24504)------------------------------
% 1.45/0.57  % (24504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (24504)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  
% 1.45/0.57  % (24504)Memory used [KB]: 10618
% 1.45/0.57  % (24504)Time elapsed: 0.154 s
% 1.45/0.57  % (24504)------------------------------
% 1.45/0.57  % (24504)------------------------------
% 1.45/0.57  % (24503)Refutation not found, incomplete strategy% (24503)------------------------------
% 1.45/0.57  % (24503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (24503)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  
% 1.45/0.57  % (24503)Memory used [KB]: 10618
% 1.45/0.57  % (24503)Time elapsed: 0.151 s
% 1.45/0.57  % (24503)------------------------------
% 1.45/0.57  % (24503)------------------------------
% 1.45/0.58  % (24521)Refutation not found, incomplete strategy% (24521)------------------------------
% 1.45/0.58  % (24521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.58  % (24521)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.58  
% 1.45/0.58  % (24521)Memory used [KB]: 6268
% 1.45/0.58  % (24521)Time elapsed: 0.155 s
% 1.45/0.58  % (24521)------------------------------
% 1.45/0.58  % (24521)------------------------------
% 1.45/0.58  % (24516)Refutation not found, incomplete strategy% (24516)------------------------------
% 1.45/0.58  % (24516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.58  % (24516)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.58  
% 1.45/0.58  % (24516)Memory used [KB]: 10746
% 1.45/0.58  % (24516)Time elapsed: 0.156 s
% 1.45/0.58  % (24516)------------------------------
% 1.45/0.58  % (24516)------------------------------
% 1.45/0.58  % (24517)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.45/0.58  % (24517)Refutation not found, incomplete strategy% (24517)------------------------------
% 1.45/0.58  % (24517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.58  % (24517)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.58  
% 1.45/0.58  % (24517)Memory used [KB]: 1663
% 1.45/0.58  % (24517)Time elapsed: 0.157 s
% 1.45/0.58  % (24517)------------------------------
% 1.45/0.58  % (24517)------------------------------
% 1.45/0.58  % (24520)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.45/0.59  % (24512)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.45/0.60  % (24512)Refutation not found, incomplete strategy% (24512)------------------------------
% 1.45/0.60  % (24512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.60  % (24512)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.60  
% 1.45/0.60  % (24512)Memory used [KB]: 10618
% 1.45/0.60  % (24512)Time elapsed: 0.176 s
% 1.45/0.60  % (24512)------------------------------
% 1.45/0.60  % (24512)------------------------------
% 1.90/0.67  % (24579)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.12/0.67  % (24575)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.12/0.67  % (24575)Refutation not found, incomplete strategy% (24575)------------------------------
% 2.12/0.67  % (24575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.67  % (24575)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.67  
% 2.12/0.67  % (24575)Memory used [KB]: 6140
% 2.12/0.67  % (24575)Time elapsed: 0.101 s
% 2.12/0.67  % (24575)------------------------------
% 2.12/0.67  % (24575)------------------------------
% 2.12/0.68  % (24583)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.12/0.68  % (24583)Refutation not found, incomplete strategy% (24583)------------------------------
% 2.12/0.68  % (24583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.68  % (24583)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.68  
% 2.12/0.68  % (24583)Memory used [KB]: 1791
% 2.12/0.68  % (24583)Time elapsed: 0.086 s
% 2.12/0.68  % (24583)------------------------------
% 2.12/0.68  % (24583)------------------------------
% 2.12/0.69  % (24576)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.12/0.69  % (24577)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.12/0.69  % (24580)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.12/0.70  % (24578)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.12/0.71  % (24584)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.12/0.72  % (24581)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.12/0.73  % (24582)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.12/0.73  % (24585)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 2.12/0.74  % (24586)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 2.65/0.79  % (24587)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 2.90/0.82  % (24591)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 2.90/0.83  % (24591)Refutation not found, incomplete strategy% (24591)------------------------------
% 2.90/0.83  % (24591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.90/0.83  % (24591)Termination reason: Refutation not found, incomplete strategy
% 2.90/0.83  
% 2.90/0.83  % (24591)Memory used [KB]: 1663
% 2.90/0.83  % (24591)Time elapsed: 0.120 s
% 2.90/0.83  % (24591)------------------------------
% 2.90/0.83  % (24591)------------------------------
% 3.09/0.89  % (24500)Time limit reached!
% 3.09/0.89  % (24500)------------------------------
% 3.09/0.89  % (24500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.09/0.89  % (24500)Termination reason: Time limit
% 3.09/0.89  
% 3.09/0.89  % (24500)Memory used [KB]: 10490
% 3.09/0.89  % (24500)Time elapsed: 0.415 s
% 3.09/0.89  % (24500)------------------------------
% 3.09/0.89  % (24500)------------------------------
% 3.09/0.92  % (24507)Time limit reached!
% 3.09/0.92  % (24507)------------------------------
% 3.09/0.92  % (24507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.09/0.92  % (24507)Termination reason: Time limit
% 3.09/0.92  % (24507)Termination phase: Saturation
% 3.09/0.92  
% 3.09/0.92  % (24507)Memory used [KB]: 10234
% 3.09/0.92  % (24507)Time elapsed: 0.500 s
% 3.09/0.92  % (24507)------------------------------
% 3.09/0.92  % (24507)------------------------------
% 3.09/0.92  % (24495)Time limit reached!
% 3.09/0.92  % (24495)------------------------------
% 3.09/0.92  % (24495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.09/0.92  % (24495)Termination reason: Time limit
% 3.09/0.92  
% 3.09/0.92  % (24495)Memory used [KB]: 8443
% 3.09/0.92  % (24495)Time elapsed: 0.504 s
% 3.09/0.92  % (24495)------------------------------
% 3.09/0.92  % (24495)------------------------------
% 3.44/0.94  % (24600)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 3.63/0.98  % (24579)Time limit reached!
% 3.63/0.98  % (24579)------------------------------
% 3.63/0.98  % (24579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.63/0.98  % (24579)Termination reason: Time limit
% 3.63/0.98  % (24579)Termination phase: Saturation
% 3.63/0.98  
% 3.63/0.98  % (24579)Memory used [KB]: 13688
% 3.63/0.98  % (24579)Time elapsed: 0.400 s
% 3.63/0.98  % (24579)------------------------------
% 3.63/0.98  % (24579)------------------------------
% 3.63/1.00  % (24616)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 3.63/1.01  % (24578)Time limit reached!
% 3.63/1.01  % (24578)------------------------------
% 3.63/1.01  % (24578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.63/1.01  % (24578)Termination reason: Time limit
% 3.63/1.01  % (24578)Termination phase: Saturation
% 3.63/1.01  
% 3.63/1.01  % (24578)Memory used [KB]: 8059
% 3.63/1.01  % (24578)Time elapsed: 0.400 s
% 3.63/1.01  % (24578)------------------------------
% 3.63/1.01  % (24578)------------------------------
% 3.63/1.03  % (24511)Time limit reached!
% 3.63/1.03  % (24511)------------------------------
% 3.63/1.03  % (24511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.63/1.03  % (24511)Termination reason: Time limit
% 3.63/1.03  
% 3.63/1.03  % (24511)Memory used [KB]: 17910
% 3.63/1.03  % (24511)Time elapsed: 0.601 s
% 3.63/1.03  % (24511)------------------------------
% 3.63/1.03  % (24511)------------------------------
% 3.63/1.03  % (24502)Time limit reached!
% 3.63/1.03  % (24502)------------------------------
% 3.63/1.03  % (24502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.63/1.03  % (24502)Termination reason: Time limit
% 3.63/1.03  
% 3.63/1.03  % (24502)Memory used [KB]: 10874
% 3.63/1.03  % (24502)Time elapsed: 0.607 s
% 3.63/1.03  % (24502)------------------------------
% 3.63/1.03  % (24502)------------------------------
% 3.63/1.04  % (24524)Time limit reached!
% 3.63/1.04  % (24524)------------------------------
% 3.63/1.04  % (24524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.63/1.04  % (24524)Termination reason: Time limit
% 3.63/1.04  % (24524)Termination phase: Saturation
% 3.63/1.04  
% 3.63/1.04  % (24524)Memory used [KB]: 10106
% 3.63/1.04  % (24524)Time elapsed: 0.600 s
% 3.63/1.04  % (24524)------------------------------
% 3.63/1.04  % (24524)------------------------------
% 4.17/1.04  % (24626)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 4.17/1.06  % (24629)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 4.17/1.06  % (24629)Refutation not found, incomplete strategy% (24629)------------------------------
% 4.17/1.06  % (24629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.17/1.06  % (24629)Termination reason: Refutation not found, incomplete strategy
% 4.17/1.06  
% 4.17/1.06  % (24629)Memory used [KB]: 6140
% 4.17/1.06  % (24629)Time elapsed: 0.115 s
% 4.17/1.06  % (24629)------------------------------
% 4.17/1.06  % (24629)------------------------------
% 5.52/1.11  % (24585)Refutation found. Thanks to Tanya!
% 5.52/1.11  % SZS status Theorem for theBenchmark
% 5.52/1.11  % SZS output start Proof for theBenchmark
% 5.52/1.11  fof(f1758,plain,(
% 5.52/1.11    $false),
% 5.52/1.11    inference(subsumption_resolution,[],[f1716,f1738])).
% 5.52/1.11  fof(f1738,plain,(
% 5.52/1.11    ( ! [X1] : (~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1)) )),
% 5.52/1.11    inference(subsumption_resolution,[],[f1546,f1729])).
% 5.52/1.11  fof(f1729,plain,(
% 5.52/1.11    ( ! [X0] : (~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,sK0))) )),
% 5.52/1.11    inference(superposition,[],[f1408,f51])).
% 5.52/1.11  fof(f51,plain,(
% 5.52/1.11    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 5.52/1.11    inference(cnf_transformation,[],[f13])).
% 5.52/1.11  fof(f13,axiom,(
% 5.52/1.11    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 5.52/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 5.52/1.11  fof(f1408,plain,(
% 5.52/1.11    ( ! [X8,X7] : (~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X7,k2_xboole_0(X8,k3_xboole_0(sK0,sK1))))) )),
% 5.52/1.11    inference(subsumption_resolution,[],[f453,f1397])).
% 5.52/1.11  fof(f1397,plain,(
% 5.52/1.11    ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 5.52/1.11    inference(global_subsumption,[],[f1076,f1384])).
% 5.52/1.11  fof(f1384,plain,(
% 5.52/1.11    ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 5.52/1.11    inference(subsumption_resolution,[],[f1375,f80])).
% 5.52/1.11  fof(f80,plain,(
% 5.52/1.11    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 5.52/1.11    inference(equality_resolution,[],[f68])).
% 5.52/1.11  fof(f68,plain,(
% 5.52/1.11    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 5.52/1.11    inference(cnf_transformation,[],[f41])).
% 5.52/1.11  fof(f41,plain,(
% 5.52/1.11    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 5.52/1.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).
% 5.52/1.11  fof(f40,plain,(
% 5.52/1.11    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 5.52/1.11    introduced(choice_axiom,[])).
% 5.52/1.11  fof(f39,plain,(
% 5.52/1.11    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 5.52/1.11    inference(rectify,[],[f38])).
% 5.52/1.11  fof(f38,plain,(
% 5.52/1.11    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 5.52/1.11    inference(flattening,[],[f37])).
% 5.52/1.11  fof(f37,plain,(
% 5.52/1.11    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 5.52/1.11    inference(nnf_transformation,[],[f4])).
% 5.52/1.11  fof(f4,axiom,(
% 5.52/1.11    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 5.52/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 5.52/1.11  fof(f1375,plain,(
% 5.52/1.11    ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)),
% 5.52/1.11    inference(superposition,[],[f406,f53])).
% 5.52/1.11  fof(f53,plain,(
% 5.52/1.11    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 5.52/1.11    inference(cnf_transformation,[],[f19])).
% 5.52/1.11  fof(f19,axiom,(
% 5.52/1.11    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.52/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 5.52/1.11  fof(f406,plain,(
% 5.52/1.11    ( ! [X0] : (~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1))) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)) )),
% 5.52/1.11    inference(resolution,[],[f226,f80])).
% 5.52/1.11  fof(f226,plain,(
% 5.52/1.11    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)),
% 5.52/1.11    inference(subsumption_resolution,[],[f214,f116])).
% 5.52/1.11  fof(f116,plain,(
% 5.52/1.11    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 5.52/1.11    inference(equality_resolution,[],[f86])).
% 5.52/1.11  fof(f86,plain,(
% 5.52/1.11    ( ! [X0] : (k3_xboole_0(sK0,sK1) != X0 | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X0),sK0) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X0),X0)) )),
% 5.52/1.11    inference(superposition,[],[f42,f70])).
% 5.52/1.11  fof(f70,plain,(
% 5.52/1.11    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 5.52/1.11    inference(cnf_transformation,[],[f41])).
% 5.52/1.11  fof(f42,plain,(
% 5.52/1.11    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 5.52/1.11    inference(cnf_transformation,[],[f30])).
% 5.52/1.11  fof(f30,plain,(
% 5.52/1.11    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 5.52/1.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f29])).
% 5.52/1.11  fof(f29,plain,(
% 5.52/1.11    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 5.52/1.11    introduced(choice_axiom,[])).
% 5.52/1.11  fof(f24,plain,(
% 5.52/1.11    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 5.52/1.11    inference(ennf_transformation,[],[f21])).
% 5.52/1.11  fof(f21,negated_conjecture,(
% 5.52/1.11    ~! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 5.52/1.11    inference(negated_conjecture,[],[f20])).
% 5.52/1.11  fof(f20,conjecture,(
% 5.52/1.11    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 5.52/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 5.52/1.11  fof(f214,plain,(
% 5.52/1.11    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1) | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 5.52/1.11    inference(resolution,[],[f122,f79])).
% 5.52/1.11  fof(f79,plain,(
% 5.52/1.11    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 5.52/1.11    inference(equality_resolution,[],[f69])).
% 5.52/1.11  fof(f69,plain,(
% 5.52/1.11    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 5.52/1.11    inference(cnf_transformation,[],[f41])).
% 5.52/1.11  fof(f122,plain,(
% 5.52/1.11    ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 5.52/1.11    inference(equality_resolution,[],[f87])).
% 5.52/1.11  fof(f87,plain,(
% 5.52/1.11    ( ! [X1] : (k3_xboole_0(sK0,sK1) != X1 | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X1),k4_xboole_0(sK0,sK1)) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X1),X1)) )),
% 5.52/1.11    inference(superposition,[],[f42,f71])).
% 5.52/1.11  fof(f71,plain,(
% 5.52/1.11    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 5.52/1.11    inference(cnf_transformation,[],[f41])).
% 5.52/1.11  fof(f1076,plain,(
% 5.52/1.11    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 5.52/1.11    inference(duplicate_literal_removal,[],[f1070])).
% 5.52/1.11  fof(f1070,plain,(
% 5.52/1.11    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 5.52/1.11    inference(superposition,[],[f294,f53])).
% 5.52/1.11  fof(f294,plain,(
% 5.52/1.11    ( ! [X1] : (r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,k3_xboole_0(sK0,sK1))) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1)) )),
% 5.52/1.11    inference(resolution,[],[f134,f79])).
% 5.52/1.11  fof(f134,plain,(
% 5.52/1.11    ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 5.52/1.11    inference(equality_resolution,[],[f88])).
% 5.52/1.11  fof(f88,plain,(
% 5.52/1.11    ( ! [X2] : (k3_xboole_0(sK0,sK1) != X2 | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X2),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X2),sK0) | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X2),X2)) )),
% 5.52/1.11    inference(superposition,[],[f42,f72])).
% 5.52/1.11  fof(f72,plain,(
% 5.52/1.11    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 5.52/1.11    inference(cnf_transformation,[],[f41])).
% 5.52/1.11  fof(f453,plain,(
% 5.52/1.11    ( ! [X8,X7] : (~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X7,k2_xboole_0(X8,k3_xboole_0(sK0,sK1)))) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)) )),
% 5.52/1.11    inference(superposition,[],[f188,f62])).
% 5.52/1.11  fof(f62,plain,(
% 5.52/1.11    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 5.52/1.11    inference(cnf_transformation,[],[f18])).
% 5.52/1.11  fof(f18,axiom,(
% 5.52/1.11    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 5.52/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 5.52/1.11  fof(f188,plain,(
% 5.52/1.11    ( ! [X0] : (~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1))) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)) )),
% 5.52/1.11    inference(resolution,[],[f116,f80])).
% 5.52/1.11  fof(f1546,plain,(
% 5.52/1.11    ( ! [X1] : (r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,sK0)) | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1)) )),
% 5.52/1.11    inference(resolution,[],[f1397,f79])).
% 5.52/1.11  fof(f1716,plain,(
% 5.52/1.11    ( ! [X0] : (r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(X0,k3_xboole_0(sK0,sK1)))) )),
% 5.52/1.11    inference(resolution,[],[f1408,f1400])).
% 5.52/1.11  fof(f1400,plain,(
% 5.52/1.11    ( ! [X1] : (r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),X1)) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1)) )),
% 5.52/1.11    inference(subsumption_resolution,[],[f189,f1397])).
% 5.52/1.11  fof(f189,plain,(
% 5.52/1.11    ( ! [X1] : (r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),X1)) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1)) )),
% 5.52/1.11    inference(resolution,[],[f116,f79])).
% 5.52/1.11  % SZS output end Proof for theBenchmark
% 5.52/1.11  % (24585)------------------------------
% 5.52/1.11  % (24585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.52/1.11  % (24585)Termination reason: Refutation
% 5.52/1.11  
% 5.52/1.11  % (24585)Memory used [KB]: 8059
% 5.52/1.11  % (24585)Time elapsed: 0.492 s
% 5.52/1.11  % (24585)------------------------------
% 5.52/1.11  % (24585)------------------------------
% 5.52/1.11  % (24491)Success in time 0.728 s
%------------------------------------------------------------------------------
