%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relset_1__t23_relset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:08 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 826 expanded)
%              Number of leaves         :   13 ( 262 expanded)
%              Depth                    :   23
%              Number of atoms          :  229 (3696 expanded)
%              Number of equality atoms :   53 ( 851 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3021,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3020,f3010])).

fof(f3010,plain,(
    r2_hidden(sK3,sK1) ),
    inference(trivial_inequality_removal,[],[f2458])).

fof(f2458,plain,
    ( sK1 != sK1
    | r2_hidden(sK3,sK1) ),
    inference(backward_demodulation,[],[f2456,f86])).

fof(f86,plain,
    ( r2_hidden(sK3,sK1)
    | k2_relat_1(sK2) != sK1 ),
    inference(backward_demodulation,[],[f80,f60])).

fof(f60,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( k2_relset_1(sK0,sK1,sK2) != sK1
      | ( ! [X4] : ~ r2_hidden(k4_tarski(X4,sK3),sK2)
        & r2_hidden(sK3,sK1) ) )
    & ( k2_relset_1(sK0,sK1,sK2) = sK1
      | ! [X5] :
          ( r2_hidden(k4_tarski(sK4(X5),X5),sK2)
          | ~ r2_hidden(X5,sK1) ) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f42,f45,f44,f43])).

fof(f43,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_relset_1(X0,X1,X2) != X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) ) )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ! [X5] :
              ( ? [X6] : r2_hidden(k4_tarski(X6,X5),X2)
              | ~ r2_hidden(X5,X1) ) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( k2_relset_1(sK0,sK1,sK2) != sK1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),sK2)
            & r2_hidden(X3,sK1) ) )
      & ( k2_relset_1(sK0,sK1,sK2) = sK1
        | ! [X5] :
            ( ? [X6] : r2_hidden(k4_tarski(X6,X5),sK2)
            | ~ r2_hidden(X5,sK1) ) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
          & r2_hidden(X3,X1) )
     => ( ! [X4] : ~ r2_hidden(k4_tarski(X4,sK3),X2)
        & r2_hidden(sK3,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X2,X5] :
      ( ? [X6] : r2_hidden(k4_tarski(X6,X5),X2)
     => r2_hidden(k4_tarski(sK4(X5),X5),X2) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X5] :
            ( ? [X6] : r2_hidden(k4_tarski(X6,X5),X2)
            | ~ r2_hidden(X5,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
      <~> k2_relset_1(X0,X1,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( ! [X3] :
              ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t23_relset_1.p',t23_relset_1)).

fof(f80,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f58,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t23_relset_1.p',redefinition_k2_relset_1)).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f2456,plain,(
    k2_relat_1(sK2) = sK1 ),
    inference(subsumption_resolution,[],[f2454,f1543])).

fof(f1543,plain,
    ( ~ r2_hidden(sK6(sK2,sK1),sK1)
    | k2_relat_1(sK2) = sK1 ),
    inference(duplicate_literal_removal,[],[f1542])).

fof(f1542,plain,
    ( ~ r2_hidden(sK6(sK2,sK1),sK1)
    | k2_relat_1(sK2) = sK1
    | k2_relat_1(sK2) = sK1 ),
    inference(factoring,[],[f236])).

fof(f236,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK6(sK2,X2),sK1)
      | ~ r2_hidden(sK6(sK2,X2),X2)
      | k2_relat_1(sK2) = X2
      | k2_relat_1(sK2) = sK1 ) ),
    inference(resolution,[],[f85,f70])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f51,f54,f53,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK7(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t23_relset_1.p',d5_relat_1)).

fof(f85,plain,(
    ! [X5] :
      ( r2_hidden(k4_tarski(sK4(X5),X5),sK2)
      | k2_relat_1(sK2) = sK1
      | ~ r2_hidden(X5,sK1) ) ),
    inference(backward_demodulation,[],[f80,f59])).

fof(f59,plain,(
    ! [X5] :
      ( k2_relset_1(sK0,sK1,sK2) = sK1
      | r2_hidden(k4_tarski(sK4(X5),X5),sK2)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f2454,plain,
    ( k2_relat_1(sK2) = sK1
    | r2_hidden(sK6(sK2,sK1),sK1) ),
    inference(duplicate_literal_removal,[],[f2448])).

fof(f2448,plain,
    ( k2_relat_1(sK2) = sK1
    | k2_relat_1(sK2) = sK1
    | r2_hidden(sK6(sK2,sK1),sK1) ),
    inference(resolution,[],[f1597,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f1597,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK6(sK2,sK1)),sK2)
      | k2_relat_1(sK2) = sK1 ) ),
    inference(resolution,[],[f1555,f78])).

fof(f78,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f1555,plain,
    ( ~ r2_hidden(sK6(sK2,sK1),k2_relat_1(sK2))
    | k2_relat_1(sK2) = sK1 ),
    inference(subsumption_resolution,[],[f1545,f122])).

fof(f122,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k2_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f121,f95])).

fof(f95,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK2))
      | ~ v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f88,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t23_relset_1.p',t5_subset)).

fof(f88,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(forward_demodulation,[],[f81,f80])).

fof(f81,plain,(
    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f58,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t23_relset_1.p',dt_k2_relset_1)).

fof(f121,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK2))
      | r2_hidden(X0,sK1)
      | v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f96,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t23_relset_1.p',t2_subset)).

fof(f96,plain,(
    ! [X1] :
      ( m1_subset_1(X1,sK1)
      | ~ r2_hidden(X1,k2_relat_1(sK2)) ) ),
    inference(resolution,[],[f88,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t23_relset_1.p',t4_subset)).

fof(f1545,plain,
    ( ~ r2_hidden(sK6(sK2,sK1),sK1)
    | k2_relat_1(sK2) = sK1
    | ~ r2_hidden(sK6(sK2,sK1),k2_relat_1(sK2)) ),
    inference(duplicate_literal_removal,[],[f1540])).

fof(f1540,plain,
    ( ~ r2_hidden(sK6(sK2,sK1),sK1)
    | k2_relat_1(sK2) = sK1
    | k2_relat_1(sK2) = sK1
    | ~ r2_hidden(sK6(sK2,sK1),k2_relat_1(sK2)) ),
    inference(resolution,[],[f236,f122])).

fof(f3020,plain,(
    ~ r2_hidden(sK3,sK1) ),
    inference(forward_demodulation,[],[f3001,f2456])).

fof(f3001,plain,(
    ~ r2_hidden(sK3,k2_relat_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f2502])).

fof(f2502,plain,
    ( sK1 != sK1
    | ~ r2_hidden(sK3,k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f2456,f159])).

fof(f159,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK2))
    | k2_relat_1(sK2) != sK1 ),
    inference(resolution,[],[f87,f79])).

fof(f79,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f87,plain,(
    ! [X4] :
      ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
      | k2_relat_1(sK2) != sK1 ) ),
    inference(backward_demodulation,[],[f80,f61])).

fof(f61,plain,(
    ! [X4] :
      ( k2_relset_1(sK0,sK1,sK2) != sK1
      | ~ r2_hidden(k4_tarski(X4,sK3),sK2) ) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
