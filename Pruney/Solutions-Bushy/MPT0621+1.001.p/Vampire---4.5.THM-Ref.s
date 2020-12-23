%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0621+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 110 expanded)
%              Number of leaves         :   13 (  33 expanded)
%              Depth                    :   19
%              Number of atoms          :  201 ( 489 expanded)
%              Number of equality atoms :   94 ( 214 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f93,plain,(
    $false ),
    inference(subsumption_resolution,[],[f86,f42])).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f29,f30])).

fof(f30,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f29,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f86,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f28,f85])).

fof(f85,plain,(
    k1_xboole_0 = np__1 ),
    inference(subsumption_resolution,[],[f83,f27])).

fof(f27,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k1_xboole_0 != sK0
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK0
            | k1_relat_1(X1) != sK0
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k1_relat_1(X2) != X0
                | k1_relat_1(X1) != X0
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
   => ( k1_xboole_0 != sK0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK0
              | k1_relat_1(X1) != sK0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k1_relat_1(X2) = X0
                    & k1_relat_1(X1) = X0 )
                 => X1 = X2 ) ) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( k1_relat_1(X2) = X0
                  & k1_relat_1(X1) = X0 )
               => X1 = X2 ) ) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).

fof(f83,plain,
    ( k1_xboole_0 = np__1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f82,f68])).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_funct_1(sK2(X0),sK1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f60,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f60,plain,(
    ! [X1] :
      ( v1_xboole_0(X1)
      | k1_xboole_0 = k1_funct_1(sK2(X1),sK1(X1)) ) ),
    inference(resolution,[],[f54,f36])).

fof(f36,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | k1_xboole_0 = k1_funct_1(sK2(X0),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK2(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK2(X0)) = X0
      & v1_funct_1(sK2(X0))
      & v1_relat_1(sK2(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK2(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK2(X0)) = X0
        & v1_funct_1(sK2(X0))
        & v1_relat_1(sK2(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f41,f32])).

fof(f32,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f3,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f82,plain,(
    np__1 = k1_funct_1(sK2(sK0),sK1(sK0)) ),
    inference(subsumption_resolution,[],[f76,f27])).

fof(f76,plain,
    ( np__1 = k1_funct_1(sK2(sK0),sK1(sK0))
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f66,f73])).

fof(f73,plain,(
    sK2(sK0) = sK3(sK0) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( sK0 != X0
      | sK2(X0) = sK3(sK0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK3(X0) = sK2(X1)
      | sK0 != X1 ) ),
    inference(superposition,[],[f52,f39])).

fof(f39,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X2] :
          ( np__1 = k1_funct_1(sK3(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK3(X0)) = X0
      & v1_funct_1(sK3(X0))
      & v1_relat_1(sK3(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_funct_1(X1,X2) = np__1
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( np__1 = k1_funct_1(sK3(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK3(X0)) = X0
        & v1_funct_1(sK3(X0))
        & v1_relat_1(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = np__1 )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

fof(f52,plain,(
    ! [X2,X3] :
      ( sK0 != k1_relat_1(sK3(X2))
      | sK3(X2) = sK2(X3)
      | sK0 != X3 ) ),
    inference(subsumption_resolution,[],[f50,f37])).

fof(f37,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f50,plain,(
    ! [X2,X3] :
      ( sK0 != k1_relat_1(sK3(X2))
      | sK3(X2) = sK2(X3)
      | sK0 != X3
      | ~ v1_relat_1(sK3(X2)) ) ),
    inference(resolution,[],[f45,f38])).

fof(f38,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k1_relat_1(X1) != sK0
      | sK2(X0) = X1
      | sK0 != X0
      | ~ v1_relat_1(X1) ) ),
    inference(forward_demodulation,[],[f44,f35])).

fof(f35,plain,(
    ! [X0] : k1_relat_1(sK2(X0)) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X0,X1] :
      ( sK0 != k1_relat_1(sK2(X0))
      | k1_relat_1(X1) != sK0
      | sK2(X0) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f43,f33])).

fof(f33,plain,(
    ! [X0] : v1_relat_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    ! [X0,X1] :
      ( sK0 != k1_relat_1(sK2(X0))
      | k1_relat_1(X1) != sK0
      | sK2(X0) = X1
      | ~ v1_relat_1(sK2(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f34,f26])).

fof(f26,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | k1_relat_1(X2) != sK0
      | k1_relat_1(X1) != sK0
      | X1 = X2
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f34,plain,(
    ! [X0] : v1_funct_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,(
    ! [X0] :
      ( np__1 = k1_funct_1(sK3(X0),sK1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f59,f31])).

fof(f59,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | np__1 = k1_funct_1(sK3(X0),sK1(X0)) ) ),
    inference(resolution,[],[f54,f40])).

fof(f40,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | np__1 = k1_funct_1(sK3(X0),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f28,plain,(
    ~ v1_xboole_0(np__1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ~ v1_xboole_0(np__1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',spc1_boole)).

%------------------------------------------------------------------------------
