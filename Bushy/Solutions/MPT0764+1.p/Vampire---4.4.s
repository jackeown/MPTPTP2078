%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord1__t10_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:10 EDT 2019

% Result     : Theorem 4.62s
% Output     : Refutation 4.62s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 735 expanded)
%              Number of leaves         :   20 ( 261 expanded)
%              Depth                    :   18
%              Number of atoms          :  537 (4703 expanded)
%              Number of equality atoms :   78 ( 613 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7030,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6803,f1014])).

fof(f1014,plain,(
    r2_hidden(k4_tarski(sK5(sK0,sK1),sK5(sK0,sK1)),sK0) ),
    inference(subsumption_resolution,[],[f1013,f83])).

fof(f83,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( ! [X2] :
        ( ( ~ r2_hidden(k4_tarski(X2,sK2(X2)),sK0)
          & r2_hidden(sK2(X2),sK1) )
        | ~ r2_hidden(X2,sK1) )
    & k1_xboole_0 != sK1
    & r1_tarski(sK1,k3_relat_1(sK0))
    & v2_wellord1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f56,f55,f54])).

fof(f54,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                    & r2_hidden(X3,X1) )
                | ~ r2_hidden(X2,X1) )
            & k1_xboole_0 != X1
            & r1_tarski(X1,k3_relat_1(X0)) )
        & v2_wellord1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),sK0)
                  & r2_hidden(X3,X1) )
              | ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1
          & r1_tarski(X1,k3_relat_1(sK0)) )
      & v2_wellord1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                  & r2_hidden(X3,X1) )
              | ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1
          & r1_tarski(X1,k3_relat_1(X0)) )
     => ( ! [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,sK1) )
            | ~ r2_hidden(X2,sK1) )
        & k1_xboole_0 != sK1
        & r1_tarski(sK1,k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X3,X1) )
     => ( ~ r2_hidden(k4_tarski(X2,sK2(X2)),X0)
        & r2_hidden(sK2(X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                  & r2_hidden(X3,X1) )
              | ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1
          & r1_tarski(X1,k3_relat_1(X0)) )
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                  & r2_hidden(X3,X1) )
              | ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1
          & r1_tarski(X1,k3_relat_1(X0)) )
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v2_wellord1(X0)
         => ! [X1] :
              ~ ( ! [X2] :
                    ~ ( ! [X3] :
                          ( r2_hidden(X3,X1)
                         => r2_hidden(k4_tarski(X2,X3),X0) )
                      & r2_hidden(X2,X1) )
                & k1_xboole_0 != X1
                & r1_tarski(X1,k3_relat_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( ! [X2] :
                  ~ ( ! [X3] :
                        ( r2_hidden(X3,X1)
                       => r2_hidden(k4_tarski(X2,X3),X0) )
                    & r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t10_wellord1.p',t10_wellord1)).

fof(f1013,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK1),sK5(sK0,sK1)),sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f999,f164])).

fof(f164,plain,(
    v1_relat_2(sK0) ),
    inference(subsumption_resolution,[],[f152,f84])).

fof(f84,plain,(
    v2_wellord1(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f152,plain,
    ( v1_relat_2(sK0)
    | ~ v2_wellord1(sK0) ),
    inference(resolution,[],[f83,f105])).

fof(f105,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t10_wellord1.p',d4_wellord1)).

fof(f999,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK1),sK5(sK0,sK1)),sK0)
    | ~ v1_relat_2(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f808,f91])).

fof(f91,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,X2),X0)
      | ~ r2_hidden(X2,k3_relat_1(X0))
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK3(X0),sK3(X0)),X0)
            & r2_hidden(sK3(X0),k3_relat_1(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f59,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k4_tarski(X1,X1),X0)
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK3(X0),sK3(X0)),X0)
        & r2_hidden(sK3(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ? [X1] :
              ( ~ r2_hidden(k4_tarski(X1,X1),X0)
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ? [X1] :
              ( ~ r2_hidden(k4_tarski(X1,X1),X0)
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X1] :
              ( r2_hidden(k4_tarski(X1,X1),X0)
              | ~ r2_hidden(X1,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(k4_tarski(X1,X1),X0)
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k3_relat_1(X0))
           => r2_hidden(k4_tarski(X1,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t10_wellord1.p',l1_wellord1)).

fof(f808,plain,(
    r2_hidden(sK5(sK0,sK1),k3_relat_1(sK0)) ),
    inference(resolution,[],[f716,f180])).

fof(f180,plain,(
    r2_hidden(sK5(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f179,f83])).

fof(f179,plain,
    ( r2_hidden(sK5(sK0,sK1),sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f178,f168])).

fof(f168,plain,(
    v1_wellord1(sK0) ),
    inference(subsumption_resolution,[],[f156,f84])).

fof(f156,plain,
    ( v1_wellord1(sK0)
    | ~ v2_wellord1(sK0) ),
    inference(resolution,[],[f83,f109])).

fof(f109,plain,(
    ! [X0] :
      ( v1_wellord1(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f178,plain,
    ( r2_hidden(sK5(sK0,sK1),sK1)
    | ~ v1_wellord1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f175,f86])).

fof(f86,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f57])).

fof(f175,plain,
    ( r2_hidden(sK5(sK0,sK1),sK1)
    | k1_xboole_0 = sK1
    | ~ v1_wellord1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f85,f94])).

fof(f94,plain,(
    ! [X0,X3] :
      ( r2_hidden(sK5(X0,X3),X3)
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k3_relat_1(X0))
      | ~ v1_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ( ( v1_wellord1(X0)
          | ( ! [X2] :
                ( ~ r1_xboole_0(k1_wellord1(X0,X2),sK4(X0))
                | ~ r2_hidden(X2,sK4(X0)) )
            & k1_xboole_0 != sK4(X0)
            & r1_tarski(sK4(X0),k3_relat_1(X0)) ) )
        & ( ! [X3] :
              ( ( r1_xboole_0(k1_wellord1(X0,sK5(X0,X3)),X3)
                & r2_hidden(sK5(X0,X3),X3) )
              | k1_xboole_0 = X3
              | ~ r1_tarski(X3,k3_relat_1(X0)) )
          | ~ v1_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f63,f65,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r1_xboole_0(k1_wellord1(X0,X2),X1)
              | ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1
          & r1_tarski(X1,k3_relat_1(X0)) )
     => ( ! [X2] :
            ( ~ r1_xboole_0(k1_wellord1(X0,X2),sK4(X0))
            | ~ r2_hidden(X2,sK4(X0)) )
        & k1_xboole_0 != sK4(X0)
        & r1_tarski(sK4(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( r1_xboole_0(k1_wellord1(X0,X4),X3)
          & r2_hidden(X4,X3) )
     => ( r1_xboole_0(k1_wellord1(X0,sK5(X0,X3)),X3)
        & r2_hidden(sK5(X0,X3),X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ( ( v1_wellord1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ r1_xboole_0(k1_wellord1(X0,X2),X1)
                  | ~ r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) )
        & ( ! [X3] :
              ( ? [X4] :
                  ( r1_xboole_0(k1_wellord1(X0,X4),X3)
                  & r2_hidden(X4,X3) )
              | k1_xboole_0 = X3
              | ~ r1_tarski(X3,k3_relat_1(X0)) )
          | ~ v1_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ( ( v1_wellord1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ r1_xboole_0(k1_wellord1(X0,X2),X1)
                  | ~ r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) )
        & ( ! [X1] :
              ( ? [X2] :
                  ( r1_xboole_0(k1_wellord1(X0,X2),X1)
                  & r2_hidden(X2,X1) )
              | k1_xboole_0 = X1
              | ~ r1_tarski(X1,k3_relat_1(X0)) )
          | ~ v1_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_wellord1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( r1_xboole_0(k1_wellord1(X0,X2),X1)
                & r2_hidden(X2,X1) )
            | k1_xboole_0 = X1
            | ~ r1_tarski(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_wellord1(X0)
      <=> ! [X1] :
            ~ ( ! [X2] :
                  ~ ( r1_xboole_0(k1_wellord1(X0,X2),X1)
                    & r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t10_wellord1.p',d2_wellord1)).

fof(f85,plain,(
    r1_tarski(sK1,k3_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f57])).

fof(f716,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,k3_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f715,f261])).

fof(f261,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k3_relat_1(sK0))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f177,f133])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t10_wellord1.p',t5_subset)).

fof(f177,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k3_relat_1(sK0))) ),
    inference(resolution,[],[f85,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t10_wellord1.p',t3_subset)).

fof(f715,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,k3_relat_1(sK0))
      | v1_xboole_0(k3_relat_1(sK0)) ) ),
    inference(resolution,[],[f262,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t10_wellord1.p',t2_subset)).

fof(f262,plain,(
    ! [X1] :
      ( m1_subset_1(X1,k3_relat_1(sK0))
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f177,f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t10_wellord1.p',t4_subset)).

fof(f6803,plain,(
    ~ r2_hidden(k4_tarski(sK5(sK0,sK1),sK5(sK0,sK1)),sK0) ),
    inference(backward_demodulation,[],[f6802,f265])).

fof(f265,plain,(
    ~ r2_hidden(k4_tarski(sK5(sK0,sK1),sK2(sK5(sK0,sK1))),sK0) ),
    inference(resolution,[],[f180,f88])).

fof(f88,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | ~ r2_hidden(k4_tarski(X2,sK2(X2)),sK0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f6802,plain,(
    sK2(sK5(sK0,sK1)) = sK5(sK0,sK1) ),
    inference(subsumption_resolution,[],[f6801,f1054])).

fof(f1054,plain,
    ( r2_hidden(k4_tarski(sK2(sK5(sK0,sK1)),sK5(sK0,sK1)),sK0)
    | sK2(sK5(sK0,sK1)) = sK5(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1053,f83])).

fof(f1053,plain,
    ( r2_hidden(k4_tarski(sK2(sK5(sK0,sK1)),sK5(sK0,sK1)),sK0)
    | sK2(sK5(sK0,sK1)) = sK5(sK0,sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f1052,f167])).

fof(f167,plain,(
    v6_relat_2(sK0) ),
    inference(subsumption_resolution,[],[f155,f84])).

fof(f155,plain,
    ( v6_relat_2(sK0)
    | ~ v2_wellord1(sK0) ),
    inference(resolution,[],[f83,f108])).

fof(f108,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f1052,plain,
    ( r2_hidden(k4_tarski(sK2(sK5(sK0,sK1)),sK5(sK0,sK1)),sK0)
    | sK2(sK5(sK0,sK1)) = sK5(sK0,sK1)
    | ~ v6_relat_2(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f1051,f808])).

fof(f1051,plain,
    ( r2_hidden(k4_tarski(sK2(sK5(sK0,sK1)),sK5(sK0,sK1)),sK0)
    | sK2(sK5(sK0,sK1)) = sK5(sK0,sK1)
    | ~ r2_hidden(sK5(sK0,sK1),k3_relat_1(sK0))
    | ~ v6_relat_2(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f1046,f806])).

fof(f806,plain,(
    r2_hidden(sK2(sK5(sK0,sK1)),k3_relat_1(sK0)) ),
    inference(resolution,[],[f716,f266])).

fof(f266,plain,(
    r2_hidden(sK2(sK5(sK0,sK1)),sK1) ),
    inference(resolution,[],[f180,f87])).

fof(f87,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | r2_hidden(sK2(X2),sK1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f1046,plain,
    ( r2_hidden(k4_tarski(sK2(sK5(sK0,sK1)),sK5(sK0,sK1)),sK0)
    | sK2(sK5(sK0,sK1)) = sK5(sK0,sK1)
    | ~ r2_hidden(sK2(sK5(sK0,sK1)),k3_relat_1(sK0))
    | ~ r2_hidden(sK5(sK0,sK1),k3_relat_1(sK0))
    | ~ v6_relat_2(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f265,f99])).

fof(f99,plain,(
    ! [X4,X0,X3] :
      ( r2_hidden(k4_tarski(X4,X3),X0)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | X3 = X4
      | ~ r2_hidden(X4,k3_relat_1(X0))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK7(X0),sK6(X0)),X0)
            & ~ r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)
            & sK6(X0) != sK7(X0)
            & r2_hidden(sK7(X0),k3_relat_1(X0))
            & r2_hidden(sK6(X0),k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f68,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(k4_tarski(X2,X1),X0)
          & ~ r2_hidden(k4_tarski(X1,X2),X0)
          & X1 != X2
          & r2_hidden(X2,k3_relat_1(X0))
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK7(X0),sK6(X0)),X0)
        & ~ r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)
        & sK6(X0) != sK7(X0)
        & r2_hidden(sK7(X0),k3_relat_1(X0))
        & r2_hidden(sK6(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( r2_hidden(k4_tarski(X2,X1),X0)
              | r2_hidden(k4_tarski(X1,X2),X0)
              | X1 = X2
              | ~ r2_hidden(X2,k3_relat_1(X0))
              | ~ r2_hidden(X1,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ~ ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t10_wellord1.p',l4_wellord1)).

fof(f6801,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK5(sK0,sK1)),sK5(sK0,sK1)),sK0)
    | sK2(sK5(sK0,sK1)) = sK5(sK0,sK1) ),
    inference(subsumption_resolution,[],[f6787,f83])).

fof(f6787,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK5(sK0,sK1)),sK5(sK0,sK1)),sK0)
    | sK2(sK5(sK0,sK1)) = sK5(sK0,sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f1066,f134])).

fof(f134,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK8(X0,X1,X2),X1),X0)
                | sK8(X0,X1,X2) = X1
                | ~ r2_hidden(sK8(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK8(X0,X1,X2),X1),X0)
                  & sK8(X0,X1,X2) != X1 )
                | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f75,f76])).

fof(f76,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK8(X0,X1,X2),X1),X0)
          | sK8(X0,X1,X2) = X1
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK8(X0,X1,X2),X1),X0)
            & sK8(X0,X1,X2) != X1 )
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t10_wellord1.p',d1_wellord1)).

fof(f1066,plain,(
    ~ r2_hidden(sK2(sK5(sK0,sK1)),k1_wellord1(sK0,sK5(sK0,sK1))) ),
    inference(resolution,[],[f294,f266])).

fof(f294,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k1_wellord1(sK0,sK5(sK0,sK1))) ) ),
    inference(resolution,[],[f183,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK10(X0,X1),X1)
          & r2_hidden(sK10(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f43,f80])).

fof(f80,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK10(X0,X1),X1)
        & r2_hidden(sK10(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t10_wellord1.p',t3_xboole_0)).

fof(f183,plain,(
    r1_xboole_0(k1_wellord1(sK0,sK5(sK0,sK1)),sK1) ),
    inference(subsumption_resolution,[],[f182,f83])).

fof(f182,plain,
    ( r1_xboole_0(k1_wellord1(sK0,sK5(sK0,sK1)),sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f181,f168])).

fof(f181,plain,
    ( r1_xboole_0(k1_wellord1(sK0,sK5(sK0,sK1)),sK1)
    | ~ v1_wellord1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f176,f86])).

fof(f176,plain,
    ( r1_xboole_0(k1_wellord1(sK0,sK5(sK0,sK1)),sK1)
    | k1_xboole_0 = sK1
    | ~ v1_wellord1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f85,f95])).

fof(f95,plain,(
    ! [X0,X3] :
      ( r1_xboole_0(k1_wellord1(X0,sK5(X0,X3)),X3)
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k3_relat_1(X0))
      | ~ v1_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f66])).
%------------------------------------------------------------------------------
