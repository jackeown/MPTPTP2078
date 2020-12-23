%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  115 (1407 expanded)
%              Number of leaves         :   14 ( 412 expanded)
%              Depth                    :   27
%              Number of atoms          :  418 (7588 expanded)
%              Number of equality atoms :  105 (1335 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f728,plain,(
    $false ),
    inference(subsumption_resolution,[],[f724,f43])).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f724,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f126,f723])).

fof(f723,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f691,f43])).

fof(f691,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f471,f654])).

fof(f654,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f623,f43])).

fof(f623,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f125,f605])).

fof(f605,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f595,f567])).

fof(f567,plain,(
    v1_funct_2(sK3,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f39,f565])).

fof(f565,plain,(
    k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f561])).

fof(f561,plain,
    ( k1_xboole_0 = sK1
    | sK4 != sK4 ),
    inference(resolution,[],[f557,f121])).

fof(f121,plain,(
    r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    inference(subsumption_resolution,[],[f119,f40])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ! [X5] :
        ( k1_funct_1(sK3,X5) != sK4
        | ~ r2_hidden(X5,sK2)
        | ~ m1_subset_1(X5,sK0) )
    & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f13,f24,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK3,X5) != X4
              | ~ r2_hidden(X5,sK2)
              | ~ m1_subset_1(X5,sK0) )
          & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X4] :
        ( ! [X5] :
            ( k1_funct_1(sK3,X5) != X4
            | ~ r2_hidden(X5,sK2)
            | ~ m1_subset_1(X5,sK0) )
        & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
   => ( ! [X5] :
          ( k1_funct_1(sK3,X5) != sK4
          | ~ r2_hidden(X5,sK2)
          | ~ m1_subset_1(X5,sK0) )
      & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

fof(f119,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f41,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f41,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f557,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k9_relat_1(sK3,sK2))
      | k1_xboole_0 = sK1
      | sK4 != X0 ) ),
    inference(duplicate_literal_removal,[],[f551])).

fof(f551,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k9_relat_1(sK3,sK2))
      | k1_xboole_0 = sK1
      | ~ r2_hidden(X0,k9_relat_1(sK3,sK2))
      | sK4 != X0 ) ),
    inference(resolution,[],[f288,f198])).

fof(f198,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK6(X0,sK2,sK3),sK0)
      | ~ r2_hidden(X0,k9_relat_1(sK3,sK2))
      | sK4 != X0 ) ),
    inference(subsumption_resolution,[],[f197,f83])).

fof(f83,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f54,f40])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f197,plain,(
    ! [X0] :
      ( sK4 != X0
      | ~ r2_hidden(X0,k9_relat_1(sK3,sK2))
      | ~ r2_hidden(sK6(X0,sK2,sK3),sK0)
      | ~ v1_relat_1(sK3) ) ),
    inference(duplicate_literal_removal,[],[f196])).

fof(f196,plain,(
    ! [X0] :
      ( sK4 != X0
      | ~ r2_hidden(X0,k9_relat_1(sK3,sK2))
      | ~ r2_hidden(sK6(X0,sK2,sK3),sK0)
      | ~ r2_hidden(X0,k9_relat_1(sK3,sK2))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f195,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)
            & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)
        & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f195,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK6(X2,X3,sK3),sK2)
      | sK4 != X2
      | ~ r2_hidden(X2,k9_relat_1(sK3,X3))
      | ~ r2_hidden(sK6(X2,X3,sK3),sK0) ) ),
    inference(resolution,[],[f193,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f47,f44])).

fof(f44,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f193,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK6(X0,X1,sK3),sK0)
      | ~ r2_hidden(sK6(X0,X1,sK3),sK2)
      | sK4 != X0
      | ~ r2_hidden(X0,k9_relat_1(sK3,X1)) ) ),
    inference(subsumption_resolution,[],[f192,f38])).

fof(f38,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f192,plain,(
    ! [X0,X1] :
      ( sK4 != X0
      | ~ r2_hidden(sK6(X0,X1,sK3),sK2)
      | ~ m1_subset_1(sK6(X0,X1,sK3),sK0)
      | ~ r2_hidden(X0,k9_relat_1(sK3,X1))
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f189,f83])).

fof(f189,plain,(
    ! [X0,X1] :
      ( sK4 != X0
      | ~ r2_hidden(sK6(X0,X1,sK3),sK2)
      | ~ m1_subset_1(sK6(X0,X1,sK3),sK0)
      | ~ v1_relat_1(sK3)
      | ~ r2_hidden(X0,k9_relat_1(sK3,X1))
      | ~ v1_funct_1(sK3) ) ),
    inference(superposition,[],[f42,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,sK6(X0,X2,X1)) = X0
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k9_relat_1(X1,X2))
      | ~ v1_funct_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | k1_funct_1(X1,sK6(X0,X2,X1)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f51,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

% (13580)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f42,plain,(
    ! [X5] :
      ( k1_funct_1(sK3,X5) != sK4
      | ~ r2_hidden(X5,sK2)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f288,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK6(X2,X3,sK3),sK0)
      | ~ r2_hidden(X2,k9_relat_1(sK3,X3))
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f280,f83])).

fof(f280,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK6(X2,X3,sK3),sK0)
      | ~ r2_hidden(X2,k9_relat_1(sK3,X3))
      | ~ v1_relat_1(sK3)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f50,f277])).

fof(f277,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f275,f40])).

fof(f275,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f274,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f274,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f271,f39])).

fof(f271,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f56,f40])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

% (13583)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f39,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f595,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f568,f68])).

fof(f68,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f568,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f40,f565])).

fof(f125,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(subsumption_resolution,[],[f122,f83])).

fof(f122,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f120,f113])).

fof(f113,plain,(
    ! [X4,X5] :
      ( v1_xboole_0(k9_relat_1(X4,X5))
      | ~ v1_xboole_0(X4)
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f104,f45])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f104,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X6,k9_relat_1(X7,X8))
      | ~ v1_relat_1(X7)
      | ~ v1_xboole_0(X7) ) ),
    inference(resolution,[],[f51,f44])).

fof(f120,plain,(
    ~ v1_xboole_0(k9_relat_1(sK3,sK2)) ),
    inference(subsumption_resolution,[],[f118,f40])).

fof(f118,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK3,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f73,f65])).

fof(f73,plain,(
    ~ v1_xboole_0(k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(resolution,[],[f44,f41])).

fof(f471,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f465,f357])).

fof(f357,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_xboole_0(sK0) ),
    inference(superposition,[],[f40,f355])).

fof(f355,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f318,f43])).

fof(f318,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK0
    | ~ v1_xboole_0(sK0) ),
    inference(superposition,[],[f125,f303])).

fof(f303,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | ~ v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f298,f289])).

fof(f289,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ v1_xboole_0(sK0) ),
    inference(superposition,[],[f39,f279])).

fof(f279,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_xboole_0(sK0) ),
    inference(superposition,[],[f126,f277])).

fof(f298,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f290,f68])).

fof(f290,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ v1_xboole_0(sK0) ),
    inference(superposition,[],[f40,f279])).

fof(f465,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ v1_xboole_0(sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(superposition,[],[f428,f55])).

fof(f428,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f417,f356])).

fof(f356,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ v1_xboole_0(sK0) ),
    inference(superposition,[],[f39,f355])).

fof(f417,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ v1_funct_2(sK3,k1_xboole_0,sK1)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) ),
    inference(resolution,[],[f357,f70])).

fof(f70,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f126,plain,(
    ~ v1_xboole_0(k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f123,f83])).

fof(f123,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f120,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k9_relat_1(X0,X1))
      | ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f97,f45])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(k1_relat_1(X1)) ) ),
    inference(resolution,[],[f50,f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:48:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (13568)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.47  % (13569)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.47  % (13567)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.47  % (13567)Refutation not found, incomplete strategy% (13567)------------------------------
% 0.22/0.47  % (13567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (13581)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (13567)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (13567)Memory used [KB]: 10618
% 0.22/0.48  % (13567)Time elapsed: 0.052 s
% 0.22/0.48  % (13567)------------------------------
% 0.22/0.48  % (13567)------------------------------
% 0.22/0.49  % (13586)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.49  % (13575)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.49  % (13587)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.49  % (13572)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (13582)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (13586)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (13581)Refutation not found, incomplete strategy% (13581)------------------------------
% 0.22/0.50  % (13581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (13581)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (13581)Memory used [KB]: 1663
% 0.22/0.50  % (13581)Time elapsed: 0.089 s
% 0.22/0.50  % (13581)------------------------------
% 0.22/0.50  % (13581)------------------------------
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f728,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(subsumption_resolution,[],[f724,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.50  fof(f724,plain,(
% 0.22/0.50    ~v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    inference(backward_demodulation,[],[f126,f723])).
% 0.22/0.50  fof(f723,plain,(
% 0.22/0.50    k1_xboole_0 = k1_relat_1(sK3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f691,f43])).
% 0.22/0.50  fof(f691,plain,(
% 0.22/0.50    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k1_relat_1(sK3)),
% 0.22/0.50    inference(backward_demodulation,[],[f471,f654])).
% 0.22/0.50  fof(f654,plain,(
% 0.22/0.50    k1_xboole_0 = sK0),
% 0.22/0.50    inference(subsumption_resolution,[],[f623,f43])).
% 0.22/0.50  fof(f623,plain,(
% 0.22/0.50    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK0),
% 0.22/0.50    inference(superposition,[],[f125,f605])).
% 0.22/0.50  fof(f605,plain,(
% 0.22/0.50    k1_xboole_0 = sK3 | k1_xboole_0 = sK0),
% 0.22/0.50    inference(subsumption_resolution,[],[f595,f567])).
% 0.22/0.50  fof(f567,plain,(
% 0.22/0.50    v1_funct_2(sK3,sK0,k1_xboole_0)),
% 0.22/0.50    inference(backward_demodulation,[],[f39,f565])).
% 0.22/0.50  fof(f565,plain,(
% 0.22/0.50    k1_xboole_0 = sK1),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f561])).
% 0.22/0.50  fof(f561,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | sK4 != sK4),
% 0.22/0.50    inference(resolution,[],[f557,f121])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.22/0.50    inference(subsumption_resolution,[],[f119,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f13,f24,f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) => (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.22/0.50    inference(flattening,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.22/0.50    inference(negated_conjecture,[],[f10])).
% 0.22/0.50  fof(f10,conjecture,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    inference(superposition,[],[f41,f65])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f557,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k9_relat_1(sK3,sK2)) | k1_xboole_0 = sK1 | sK4 != X0) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f551])).
% 0.22/0.50  fof(f551,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k9_relat_1(sK3,sK2)) | k1_xboole_0 = sK1 | ~r2_hidden(X0,k9_relat_1(sK3,sK2)) | sK4 != X0) )),
% 0.22/0.50    inference(resolution,[],[f288,f198])).
% 0.22/0.50  fof(f198,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(sK6(X0,sK2,sK3),sK0) | ~r2_hidden(X0,k9_relat_1(sK3,sK2)) | sK4 != X0) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f197,f83])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    v1_relat_1(sK3)),
% 0.22/0.50    inference(resolution,[],[f54,f40])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.50  fof(f197,plain,(
% 0.22/0.50    ( ! [X0] : (sK4 != X0 | ~r2_hidden(X0,k9_relat_1(sK3,sK2)) | ~r2_hidden(sK6(X0,sK2,sK3),sK0) | ~v1_relat_1(sK3)) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f196])).
% 0.22/0.50  fof(f196,plain,(
% 0.22/0.50    ( ! [X0] : (sK4 != X0 | ~r2_hidden(X0,k9_relat_1(sK3,sK2)) | ~r2_hidden(sK6(X0,sK2,sK3),sK0) | ~r2_hidden(X0,k9_relat_1(sK3,sK2)) | ~v1_relat_1(sK3)) )),
% 0.22/0.50    inference(resolution,[],[f195,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f32,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(rectify,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(nnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.22/0.50  fof(f195,plain,(
% 0.22/0.50    ( ! [X2,X3] : (~r2_hidden(sK6(X2,X3,sK3),sK2) | sK4 != X2 | ~r2_hidden(X2,k9_relat_1(sK3,X3)) | ~r2_hidden(sK6(X2,X3,sK3),sK0)) )),
% 0.22/0.50    inference(resolution,[],[f193,f72])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f47,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.50    inference(rectify,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.50    inference(nnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.22/0.50    inference(nnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.50  fof(f193,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK6(X0,X1,sK3),sK0) | ~r2_hidden(sK6(X0,X1,sK3),sK2) | sK4 != X0 | ~r2_hidden(X0,k9_relat_1(sK3,X1))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f192,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    v1_funct_1(sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f192,plain,(
% 0.22/0.50    ( ! [X0,X1] : (sK4 != X0 | ~r2_hidden(sK6(X0,X1,sK3),sK2) | ~m1_subset_1(sK6(X0,X1,sK3),sK0) | ~r2_hidden(X0,k9_relat_1(sK3,X1)) | ~v1_funct_1(sK3)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f189,f83])).
% 0.22/0.50  fof(f189,plain,(
% 0.22/0.50    ( ! [X0,X1] : (sK4 != X0 | ~r2_hidden(sK6(X0,X1,sK3),sK2) | ~m1_subset_1(sK6(X0,X1,sK3),sK0) | ~v1_relat_1(sK3) | ~r2_hidden(X0,k9_relat_1(sK3,X1)) | ~v1_funct_1(sK3)) )),
% 0.22/0.50    inference(superposition,[],[f42,f111])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_funct_1(X1,sK6(X0,X2,X1)) = X0 | ~v1_relat_1(X1) | ~r2_hidden(X0,k9_relat_1(X1,X2)) | ~v1_funct_1(X1)) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f102])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X1,X2)) | ~v1_relat_1(X1) | k1_funct_1(X1,sK6(X0,X2,X1)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(resolution,[],[f51,f63])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(flattening,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(nnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  % (13580)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f288,plain,(
% 0.22/0.50    ( ! [X2,X3] : (r2_hidden(sK6(X2,X3,sK3),sK0) | ~r2_hidden(X2,k9_relat_1(sK3,X3)) | k1_xboole_0 = sK1) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f280,f83])).
% 0.22/0.50  fof(f280,plain,(
% 0.22/0.50    ( ! [X2,X3] : (r2_hidden(sK6(X2,X3,sK3),sK0) | ~r2_hidden(X2,k9_relat_1(sK3,X3)) | ~v1_relat_1(sK3) | k1_xboole_0 = sK1) )),
% 0.22/0.50    inference(superposition,[],[f50,f277])).
% 0.22/0.50  fof(f277,plain,(
% 0.22/0.50    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 0.22/0.50    inference(subsumption_resolution,[],[f275,f40])).
% 0.22/0.50  fof(f275,plain,(
% 0.22/0.50    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    inference(superposition,[],[f274,f55])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.50  fof(f274,plain,(
% 0.22/0.50    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 0.22/0.50    inference(subsumption_resolution,[],[f271,f39])).
% 0.22/0.50  fof(f271,plain,(
% 0.22/0.50    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.50    inference(resolution,[],[f56,f40])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(nnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(flattening,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  % (13583)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f595,plain,(
% 0.22/0.50    ~v1_funct_2(sK3,sK0,k1_xboole_0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK3),
% 0.22/0.50    inference(resolution,[],[f568,f68])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 0.22/0.50    inference(equality_resolution,[],[f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f568,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.22/0.50    inference(backward_demodulation,[],[f40,f565])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    ~v1_xboole_0(sK3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f122,f83])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    ~v1_xboole_0(sK3) | ~v1_relat_1(sK3)),
% 0.22/0.50    inference(resolution,[],[f120,f113])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    ( ! [X4,X5] : (v1_xboole_0(k9_relat_1(X4,X5)) | ~v1_xboole_0(X4) | ~v1_relat_1(X4)) )),
% 0.22/0.50    inference(resolution,[],[f104,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(sK5(X0),X0) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    ( ! [X6,X8,X7] : (~r2_hidden(X6,k9_relat_1(X7,X8)) | ~v1_relat_1(X7) | ~v1_xboole_0(X7)) )),
% 0.22/0.50    inference(resolution,[],[f51,f44])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    ~v1_xboole_0(k9_relat_1(sK3,sK2))),
% 0.22/0.50    inference(subsumption_resolution,[],[f118,f40])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    ~v1_xboole_0(k9_relat_1(sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    inference(superposition,[],[f73,f65])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    ~v1_xboole_0(k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.22/0.50    inference(resolution,[],[f44,f41])).
% 0.22/0.50  fof(f471,plain,(
% 0.22/0.50    k1_xboole_0 = k1_relat_1(sK3) | ~v1_xboole_0(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f465,f357])).
% 0.22/0.50  fof(f357,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~v1_xboole_0(sK0)),
% 0.22/0.50    inference(superposition,[],[f40,f355])).
% 0.22/0.50  fof(f355,plain,(
% 0.22/0.50    k1_xboole_0 = sK0 | ~v1_xboole_0(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f318,f43])).
% 0.22/0.50  fof(f318,plain,(
% 0.22/0.50    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK0 | ~v1_xboole_0(sK0)),
% 0.22/0.50    inference(superposition,[],[f125,f303])).
% 0.22/0.50  fof(f303,plain,(
% 0.22/0.50    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | ~v1_xboole_0(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f298,f289])).
% 0.22/0.50  fof(f289,plain,(
% 0.22/0.50    v1_funct_2(sK3,sK0,k1_xboole_0) | ~v1_xboole_0(sK0)),
% 0.22/0.50    inference(superposition,[],[f39,f279])).
% 0.22/0.50  fof(f279,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | ~v1_xboole_0(sK0)),
% 0.22/0.50    inference(superposition,[],[f126,f277])).
% 0.22/0.50  fof(f298,plain,(
% 0.22/0.50    ~v1_xboole_0(sK0) | ~v1_funct_2(sK3,sK0,k1_xboole_0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK3),
% 0.22/0.50    inference(resolution,[],[f290,f68])).
% 0.22/0.50  fof(f290,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~v1_xboole_0(sK0)),
% 0.22/0.50    inference(superposition,[],[f40,f279])).
% 0.22/0.50  fof(f465,plain,(
% 0.22/0.50    k1_xboole_0 = k1_relat_1(sK3) | ~v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 0.22/0.50    inference(superposition,[],[f428,f55])).
% 0.22/0.50  fof(f428,plain,(
% 0.22/0.50    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) | ~v1_xboole_0(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f417,f356])).
% 0.22/0.50  fof(f356,plain,(
% 0.22/0.50    v1_funct_2(sK3,k1_xboole_0,sK1) | ~v1_xboole_0(sK0)),
% 0.22/0.50    inference(superposition,[],[f39,f355])).
% 0.22/0.50  fof(f417,plain,(
% 0.22/0.50    ~v1_xboole_0(sK0) | ~v1_funct_2(sK3,k1_xboole_0,sK1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)),
% 0.22/0.50    inference(resolution,[],[f357,f70])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.22/0.50    inference(equality_resolution,[],[f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    ~v1_xboole_0(k1_relat_1(sK3))),
% 0.22/0.50    inference(subsumption_resolution,[],[f123,f83])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    ~v1_xboole_0(k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 0.22/0.50    inference(resolution,[],[f120,f98])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_xboole_0(k9_relat_1(X0,X1)) | ~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(resolution,[],[f97,f45])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_xboole_0(k1_relat_1(X1))) )),
% 0.22/0.50    inference(resolution,[],[f50,f44])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (13586)------------------------------
% 0.22/0.50  % (13586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (13586)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (13586)Memory used [KB]: 1918
% 0.22/0.50  % (13586)Time elapsed: 0.085 s
% 0.22/0.50  % (13586)------------------------------
% 0.22/0.50  % (13586)------------------------------
% 0.22/0.50  % (13562)Success in time 0.141 s
%------------------------------------------------------------------------------
