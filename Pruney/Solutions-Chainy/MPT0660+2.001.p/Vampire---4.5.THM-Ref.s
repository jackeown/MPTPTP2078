%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:10 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :   52 (  63 expanded)
%              Number of leaves         :   11 (  17 expanded)
%              Depth                    :   12
%              Number of atoms          :  127 ( 141 expanded)
%              Number of equality atoms :   50 (  52 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f89,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f86])).

fof(f86,plain,(
    k6_relat_1(sK0) != k6_relat_1(sK0) ),
    inference(superposition,[],[f27,f77])).

fof(f77,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(forward_demodulation,[],[f76,f68])).

fof(f68,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k2_funct_1(k6_relat_1(X0))) ),
    inference(forward_demodulation,[],[f67,f32])).

fof(f32,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f67,plain,(
    ! [X0] : k6_relat_1(k1_relat_1(k6_relat_1(X0))) = k5_relat_1(k6_relat_1(X0),k2_funct_1(k6_relat_1(X0))) ),
    inference(subsumption_resolution,[],[f66,f29])).

fof(f29,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f66,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(k6_relat_1(X0))) = k5_relat_1(k6_relat_1(X0),k2_funct_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f65,f31])).

fof(f31,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f65,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(k6_relat_1(X0))) = k5_relat_1(k6_relat_1(X0),k2_funct_1(k6_relat_1(X0)))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f38,f28])).

fof(f28,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

fof(f38,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f76,plain,(
    ! [X0] : k2_funct_1(k6_relat_1(X0)) = k5_relat_1(k6_relat_1(X0),k2_funct_1(k6_relat_1(X0))) ),
    inference(forward_demodulation,[],[f75,f52])).

fof(f52,plain,(
    ! [X0] : k1_relat_1(k2_funct_1(k6_relat_1(X0))) = X0 ),
    inference(forward_demodulation,[],[f51,f33])).

fof(f33,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = k1_relat_1(k2_funct_1(k6_relat_1(X0))) ),
    inference(subsumption_resolution,[],[f50,f29])).

fof(f50,plain,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = k1_relat_1(k2_funct_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f49,f31])).

fof(f49,plain,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = k1_relat_1(k2_funct_1(k6_relat_1(X0)))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f36,f28])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f75,plain,(
    ! [X0] : k2_funct_1(k6_relat_1(X0)) = k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(k6_relat_1(X0)))),k2_funct_1(k6_relat_1(X0))) ),
    inference(subsumption_resolution,[],[f73,f29])).

fof(f73,plain,(
    ! [X0] :
      ( k2_funct_1(k6_relat_1(X0)) = k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(k6_relat_1(X0)))),k2_funct_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f62,f31])).

fof(f62,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | k2_funct_1(X1) = k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(X1))),k2_funct_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f57,f34])).

fof(f34,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(resolution,[],[f40,f45])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f27,plain,(
    k6_relat_1(sK0) != k2_funct_1(k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    k6_relat_1(sK0) != k2_funct_1(k6_relat_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f23])).

fof(f23,plain,
    ( ? [X0] : k6_relat_1(X0) != k2_funct_1(k6_relat_1(X0))
   => k6_relat_1(sK0) != k2_funct_1(k6_relat_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] : k6_relat_1(X0) != k2_funct_1(k6_relat_1(X0)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:04:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (1243316225)
% 0.14/0.37  ipcrm: permission denied for id (1243348994)
% 0.14/0.37  ipcrm: permission denied for id (1243381763)
% 0.14/0.38  ipcrm: permission denied for id (1243414532)
% 0.14/0.38  ipcrm: permission denied for id (1243447301)
% 0.14/0.38  ipcrm: permission denied for id (1247150087)
% 0.14/0.38  ipcrm: permission denied for id (1243545608)
% 0.14/0.38  ipcrm: permission denied for id (1243578377)
% 0.14/0.38  ipcrm: permission denied for id (1247182858)
% 0.14/0.38  ipcrm: permission denied for id (1247215627)
% 0.14/0.39  ipcrm: permission denied for id (1247248396)
% 0.14/0.39  ipcrm: permission denied for id (1243742221)
% 0.14/0.39  ipcrm: permission denied for id (1247281166)
% 0.14/0.39  ipcrm: permission denied for id (1243807759)
% 0.14/0.39  ipcrm: permission denied for id (1247313936)
% 0.14/0.39  ipcrm: permission denied for id (1250918417)
% 0.14/0.39  ipcrm: permission denied for id (1243873298)
% 0.14/0.40  ipcrm: permission denied for id (1243938836)
% 0.21/0.40  ipcrm: permission denied for id (1243971605)
% 0.21/0.40  ipcrm: permission denied for id (1244004374)
% 0.21/0.40  ipcrm: permission denied for id (1244037143)
% 0.21/0.40  ipcrm: permission denied for id (1244069912)
% 0.21/0.40  ipcrm: permission denied for id (1244102681)
% 0.21/0.40  ipcrm: permission denied for id (1244135450)
% 0.21/0.40  ipcrm: permission denied for id (1249345563)
% 0.21/0.41  ipcrm: permission denied for id (1249443869)
% 0.21/0.41  ipcrm: permission denied for id (1247543327)
% 0.21/0.41  ipcrm: permission denied for id (1251049504)
% 0.21/0.41  ipcrm: permission denied for id (1249542177)
% 0.21/0.41  ipcrm: permission denied for id (1244332066)
% 0.21/0.42  ipcrm: permission denied for id (1244364835)
% 0.21/0.42  ipcrm: permission denied for id (1247641636)
% 0.21/0.42  ipcrm: permission denied for id (1244430373)
% 0.21/0.42  ipcrm: permission denied for id (1244463142)
% 0.21/0.42  ipcrm: permission denied for id (1250492455)
% 0.21/0.42  ipcrm: permission denied for id (1247707176)
% 0.21/0.42  ipcrm: permission denied for id (1244528681)
% 0.21/0.42  ipcrm: permission denied for id (1244561450)
% 0.21/0.43  ipcrm: permission denied for id (1247739947)
% 0.21/0.43  ipcrm: permission denied for id (1249607724)
% 0.21/0.43  ipcrm: permission denied for id (1247805485)
% 0.21/0.43  ipcrm: permission denied for id (1251082286)
% 0.21/0.43  ipcrm: permission denied for id (1244725295)
% 0.21/0.43  ipcrm: permission denied for id (1244758064)
% 0.21/0.43  ipcrm: permission denied for id (1244790833)
% 0.21/0.43  ipcrm: permission denied for id (1247871026)
% 0.21/0.44  ipcrm: permission denied for id (1244856371)
% 0.21/0.44  ipcrm: permission denied for id (1247969333)
% 0.21/0.44  ipcrm: permission denied for id (1248002102)
% 0.21/0.44  ipcrm: permission denied for id (1245020216)
% 0.21/0.44  ipcrm: permission denied for id (1245052985)
% 0.21/0.44  ipcrm: permission denied for id (1245085754)
% 0.21/0.45  ipcrm: permission denied for id (1248067643)
% 0.21/0.45  ipcrm: permission denied for id (1245151292)
% 0.21/0.45  ipcrm: permission denied for id (1245184061)
% 0.21/0.45  ipcrm: permission denied for id (1245216830)
% 0.21/0.45  ipcrm: permission denied for id (1248100415)
% 0.21/0.45  ipcrm: permission denied for id (1245282368)
% 0.21/0.45  ipcrm: permission denied for id (1249738817)
% 0.21/0.45  ipcrm: permission denied for id (1245347906)
% 0.21/0.46  ipcrm: permission denied for id (1245380675)
% 0.21/0.46  ipcrm: permission denied for id (1248165956)
% 0.21/0.46  ipcrm: permission denied for id (1249771589)
% 0.21/0.46  ipcrm: permission denied for id (1245478982)
% 0.21/0.46  ipcrm: permission denied for id (1248231495)
% 0.21/0.46  ipcrm: permission denied for id (1245544520)
% 0.21/0.46  ipcrm: permission denied for id (1245577289)
% 0.21/0.47  ipcrm: permission denied for id (1250623562)
% 0.21/0.47  ipcrm: permission denied for id (1248297035)
% 0.21/0.47  ipcrm: permission denied for id (1245642828)
% 0.21/0.47  ipcrm: permission denied for id (1249837133)
% 0.21/0.47  ipcrm: permission denied for id (1245708366)
% 0.21/0.47  ipcrm: permission denied for id (1245741135)
% 0.21/0.47  ipcrm: permission denied for id (1251180624)
% 0.21/0.47  ipcrm: permission denied for id (1245806673)
% 0.21/0.48  ipcrm: permission denied for id (1245839442)
% 0.21/0.48  ipcrm: permission denied for id (1248395347)
% 0.21/0.48  ipcrm: permission denied for id (1248428116)
% 0.21/0.48  ipcrm: permission denied for id (1245904981)
% 0.21/0.48  ipcrm: permission denied for id (1245937750)
% 0.21/0.48  ipcrm: permission denied for id (1249902679)
% 0.21/0.48  ipcrm: permission denied for id (1245970520)
% 0.21/0.48  ipcrm: permission denied for id (1246003289)
% 0.21/0.49  ipcrm: permission denied for id (1249935450)
% 0.21/0.49  ipcrm: permission denied for id (1248559195)
% 0.21/0.49  ipcrm: permission denied for id (1246101596)
% 0.21/0.49  ipcrm: permission denied for id (1250689117)
% 0.21/0.49  ipcrm: permission denied for id (1248624734)
% 0.21/0.49  ipcrm: permission denied for id (1246167135)
% 0.21/0.49  ipcrm: permission denied for id (1248657504)
% 0.21/0.50  ipcrm: permission denied for id (1246232673)
% 0.21/0.50  ipcrm: permission denied for id (1251213410)
% 0.21/0.50  ipcrm: permission denied for id (1246298211)
% 0.21/0.50  ipcrm: permission denied for id (1246330980)
% 0.21/0.50  ipcrm: permission denied for id (1248723045)
% 0.21/0.50  ipcrm: permission denied for id (1250033766)
% 0.21/0.50  ipcrm: permission denied for id (1248788583)
% 0.21/0.50  ipcrm: permission denied for id (1246429288)
% 0.21/0.51  ipcrm: permission denied for id (1248821353)
% 0.21/0.51  ipcrm: permission denied for id (1250066538)
% 0.21/0.51  ipcrm: permission denied for id (1246462059)
% 0.21/0.51  ipcrm: permission denied for id (1248886892)
% 0.21/0.51  ipcrm: permission denied for id (1246527597)
% 0.21/0.51  ipcrm: permission denied for id (1246560366)
% 0.21/0.51  ipcrm: permission denied for id (1250099311)
% 0.21/0.51  ipcrm: permission denied for id (1246593136)
% 0.21/0.52  ipcrm: permission denied for id (1246625905)
% 0.21/0.52  ipcrm: permission denied for id (1246658674)
% 0.21/0.52  ipcrm: permission denied for id (1250754675)
% 0.21/0.52  ipcrm: permission denied for id (1250787444)
% 0.21/0.52  ipcrm: permission denied for id (1246756981)
% 0.21/0.52  ipcrm: permission denied for id (1249050742)
% 0.21/0.52  ipcrm: permission denied for id (1250197623)
% 0.21/0.52  ipcrm: permission denied for id (1249116280)
% 0.21/0.53  ipcrm: permission denied for id (1246855289)
% 0.21/0.53  ipcrm: permission denied for id (1250820218)
% 0.21/0.53  ipcrm: permission denied for id (1246920827)
% 0.21/0.53  ipcrm: permission denied for id (1249181820)
% 0.21/0.53  ipcrm: permission denied for id (1246986365)
% 0.21/0.53  ipcrm: permission denied for id (1247019134)
% 0.21/0.53  ipcrm: permission denied for id (1247051903)
% 1.06/0.66  % (5889)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.06/0.66  % (5888)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.06/0.66  % (5888)Refutation not found, incomplete strategy% (5888)------------------------------
% 1.06/0.66  % (5888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.06/0.66  % (5888)Termination reason: Refutation not found, incomplete strategy
% 1.06/0.66  
% 1.06/0.66  % (5888)Memory used [KB]: 6012
% 1.06/0.66  % (5888)Time elapsed: 0.076 s
% 1.06/0.66  % (5888)------------------------------
% 1.06/0.66  % (5888)------------------------------
% 1.06/0.67  % (5889)Refutation not found, incomplete strategy% (5889)------------------------------
% 1.06/0.67  % (5889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.06/0.67  % (5889)Termination reason: Refutation not found, incomplete strategy
% 1.06/0.67  
% 1.06/0.67  % (5889)Memory used [KB]: 10490
% 1.06/0.67  % (5889)Time elapsed: 0.069 s
% 1.06/0.67  % (5889)------------------------------
% 1.06/0.67  % (5889)------------------------------
% 1.06/0.67  % (5887)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.06/0.67  % (5897)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.06/0.68  % (5896)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.06/0.68  % (5896)Refutation not found, incomplete strategy% (5896)------------------------------
% 1.06/0.68  % (5896)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.06/0.68  % (5908)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.06/0.68  % (5908)Refutation found. Thanks to Tanya!
% 1.06/0.68  % SZS status Theorem for theBenchmark
% 1.06/0.68  % SZS output start Proof for theBenchmark
% 1.06/0.68  fof(f89,plain,(
% 1.06/0.68    $false),
% 1.06/0.68    inference(trivial_inequality_removal,[],[f86])).
% 1.06/0.68  fof(f86,plain,(
% 1.06/0.68    k6_relat_1(sK0) != k6_relat_1(sK0)),
% 1.06/0.68    inference(superposition,[],[f27,f77])).
% 1.06/0.68  fof(f77,plain,(
% 1.06/0.68    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 1.06/0.68    inference(forward_demodulation,[],[f76,f68])).
% 1.06/0.68  fof(f68,plain,(
% 1.06/0.68    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k2_funct_1(k6_relat_1(X0)))) )),
% 1.06/0.68    inference(forward_demodulation,[],[f67,f32])).
% 1.06/0.68  fof(f32,plain,(
% 1.06/0.68    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.06/0.68    inference(cnf_transformation,[],[f4])).
% 1.06/0.68  fof(f4,axiom,(
% 1.06/0.68    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.06/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.06/0.68  fof(f67,plain,(
% 1.06/0.68    ( ! [X0] : (k6_relat_1(k1_relat_1(k6_relat_1(X0))) = k5_relat_1(k6_relat_1(X0),k2_funct_1(k6_relat_1(X0)))) )),
% 1.06/0.68    inference(subsumption_resolution,[],[f66,f29])).
% 1.06/0.68  fof(f29,plain,(
% 1.06/0.68    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.06/0.68    inference(cnf_transformation,[],[f3])).
% 1.06/0.68  fof(f3,axiom,(
% 1.06/0.68    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.06/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.06/0.68  fof(f66,plain,(
% 1.06/0.68    ( ! [X0] : (k6_relat_1(k1_relat_1(k6_relat_1(X0))) = k5_relat_1(k6_relat_1(X0),k2_funct_1(k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.06/0.68    inference(subsumption_resolution,[],[f65,f31])).
% 1.06/0.68  fof(f31,plain,(
% 1.06/0.68    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.06/0.68    inference(cnf_transformation,[],[f7])).
% 1.06/0.68  fof(f7,axiom,(
% 1.06/0.68    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.06/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.06/0.68  fof(f65,plain,(
% 1.06/0.68    ( ! [X0] : (k6_relat_1(k1_relat_1(k6_relat_1(X0))) = k5_relat_1(k6_relat_1(X0),k2_funct_1(k6_relat_1(X0))) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.06/0.68    inference(resolution,[],[f38,f28])).
% 1.06/0.68  fof(f28,plain,(
% 1.06/0.68    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.06/0.68    inference(cnf_transformation,[],[f8])).
% 1.06/0.68  fof(f8,axiom,(
% 1.06/0.68    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 1.06/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).
% 1.06/0.68  fof(f38,plain,(
% 1.06/0.68    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.06/0.68    inference(cnf_transformation,[],[f19])).
% 1.06/0.68  fof(f19,plain,(
% 1.06/0.68    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.06/0.68    inference(flattening,[],[f18])).
% 1.06/0.68  fof(f18,plain,(
% 1.06/0.68    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.06/0.68    inference(ennf_transformation,[],[f10])).
% 1.06/0.68  fof(f10,axiom,(
% 1.06/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.06/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 1.06/0.68  fof(f76,plain,(
% 1.06/0.68    ( ! [X0] : (k2_funct_1(k6_relat_1(X0)) = k5_relat_1(k6_relat_1(X0),k2_funct_1(k6_relat_1(X0)))) )),
% 1.06/0.68    inference(forward_demodulation,[],[f75,f52])).
% 1.06/0.68  fof(f52,plain,(
% 1.06/0.68    ( ! [X0] : (k1_relat_1(k2_funct_1(k6_relat_1(X0))) = X0) )),
% 1.06/0.68    inference(forward_demodulation,[],[f51,f33])).
% 1.06/0.68  fof(f33,plain,(
% 1.06/0.68    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.06/0.68    inference(cnf_transformation,[],[f4])).
% 1.06/0.68  fof(f51,plain,(
% 1.06/0.68    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k1_relat_1(k2_funct_1(k6_relat_1(X0)))) )),
% 1.06/0.68    inference(subsumption_resolution,[],[f50,f29])).
% 1.06/0.68  fof(f50,plain,(
% 1.06/0.68    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k1_relat_1(k2_funct_1(k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.06/0.68    inference(subsumption_resolution,[],[f49,f31])).
% 1.06/0.68  fof(f49,plain,(
% 1.06/0.68    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k1_relat_1(k2_funct_1(k6_relat_1(X0))) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.06/0.68    inference(resolution,[],[f36,f28])).
% 1.06/0.68  fof(f36,plain,(
% 1.06/0.68    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.06/0.68    inference(cnf_transformation,[],[f17])).
% 1.06/0.68  fof(f17,plain,(
% 1.06/0.68    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.06/0.68    inference(flattening,[],[f16])).
% 1.06/0.68  fof(f16,plain,(
% 1.06/0.68    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.06/0.68    inference(ennf_transformation,[],[f9])).
% 1.06/0.68  fof(f9,axiom,(
% 1.06/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.06/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.06/0.68  fof(f75,plain,(
% 1.06/0.68    ( ! [X0] : (k2_funct_1(k6_relat_1(X0)) = k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(k6_relat_1(X0)))),k2_funct_1(k6_relat_1(X0)))) )),
% 1.06/0.68    inference(subsumption_resolution,[],[f73,f29])).
% 1.06/0.68  fof(f73,plain,(
% 1.06/0.68    ( ! [X0] : (k2_funct_1(k6_relat_1(X0)) = k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(k6_relat_1(X0)))),k2_funct_1(k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.06/0.68    inference(resolution,[],[f62,f31])).
% 1.06/0.68  fof(f62,plain,(
% 1.06/0.68    ( ! [X1] : (~v1_funct_1(X1) | k2_funct_1(X1) = k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(X1))),k2_funct_1(X1)) | ~v1_relat_1(X1)) )),
% 1.06/0.68    inference(resolution,[],[f57,f34])).
% 1.06/0.68  fof(f34,plain,(
% 1.06/0.68    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.06/0.68    inference(cnf_transformation,[],[f15])).
% 1.06/0.68  fof(f15,plain,(
% 1.06/0.68    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.06/0.68    inference(flattening,[],[f14])).
% 1.06/0.68  fof(f14,plain,(
% 1.06/0.68    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.06/0.68    inference(ennf_transformation,[],[f6])).
% 1.06/0.68  fof(f6,axiom,(
% 1.06/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.06/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.06/0.68  fof(f57,plain,(
% 1.06/0.68    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 1.06/0.68    inference(resolution,[],[f40,f45])).
% 1.06/0.68  fof(f45,plain,(
% 1.06/0.68    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.06/0.68    inference(equality_resolution,[],[f43])).
% 1.06/0.68  fof(f43,plain,(
% 1.06/0.68    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.06/0.68    inference(cnf_transformation,[],[f26])).
% 1.06/0.68  fof(f26,plain,(
% 1.06/0.68    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.06/0.68    inference(flattening,[],[f25])).
% 1.06/0.68  fof(f25,plain,(
% 1.06/0.68    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.06/0.68    inference(nnf_transformation,[],[f1])).
% 1.06/0.68  fof(f1,axiom,(
% 1.06/0.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.06/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.06/0.68  fof(f40,plain,(
% 1.06/0.68    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1 | ~v1_relat_1(X1)) )),
% 1.06/0.68    inference(cnf_transformation,[],[f21])).
% 1.06/0.68  fof(f21,plain,(
% 1.06/0.68    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.06/0.68    inference(flattening,[],[f20])).
% 1.06/0.68  fof(f20,plain,(
% 1.06/0.68    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.06/0.68    inference(ennf_transformation,[],[f5])).
% 1.06/0.68  fof(f5,axiom,(
% 1.06/0.68    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 1.06/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 1.06/0.68  fof(f27,plain,(
% 1.06/0.68    k6_relat_1(sK0) != k2_funct_1(k6_relat_1(sK0))),
% 1.06/0.68    inference(cnf_transformation,[],[f24])).
% 1.06/0.68  fof(f24,plain,(
% 1.06/0.68    k6_relat_1(sK0) != k2_funct_1(k6_relat_1(sK0))),
% 1.06/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f23])).
% 1.06/0.68  fof(f23,plain,(
% 1.06/0.68    ? [X0] : k6_relat_1(X0) != k2_funct_1(k6_relat_1(X0)) => k6_relat_1(sK0) != k2_funct_1(k6_relat_1(sK0))),
% 1.06/0.68    introduced(choice_axiom,[])).
% 1.06/0.68  fof(f13,plain,(
% 1.06/0.68    ? [X0] : k6_relat_1(X0) != k2_funct_1(k6_relat_1(X0))),
% 1.06/0.68    inference(ennf_transformation,[],[f12])).
% 1.06/0.68  fof(f12,negated_conjecture,(
% 1.06/0.68    ~! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 1.06/0.68    inference(negated_conjecture,[],[f11])).
% 1.06/0.68  fof(f11,conjecture,(
% 1.06/0.68    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 1.06/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).
% 1.06/0.68  % SZS output end Proof for theBenchmark
% 1.06/0.68  % (5908)------------------------------
% 1.06/0.68  % (5908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.06/0.68  % (5908)Termination reason: Refutation
% 1.06/0.68  
% 1.06/0.68  % (5908)Memory used [KB]: 10618
% 1.06/0.68  % (5908)Time elapsed: 0.097 s
% 1.06/0.68  % (5908)------------------------------
% 1.06/0.68  % (5908)------------------------------
% 1.06/0.68  % (5653)Success in time 0.319 s
%------------------------------------------------------------------------------
