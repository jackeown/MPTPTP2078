%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord2__t10_wellord2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:16 EDT 2019

% Result     : Theorem 56.04s
% Output     : Refutation 56.04s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 968 expanded)
%              Number of leaves         :   25 ( 261 expanded)
%              Depth                    :   25
%              Number of atoms          :  661 (4998 expanded)
%              Number of equality atoms :  106 (1088 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f248010,plain,(
    $false ),
    inference(subsumption_resolution,[],[f248009,f241264])).

fof(f241264,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK0,X0)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f228826,f323])).

fof(f323,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f191,f153])).

fof(f153,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t10_wellord2.p',t3_subset)).

fof(f191,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f176,f121])).

fof(f121,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK3(X0),X0)
          & r2_hidden(sK3(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f83,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK3(X0),X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t10_wellord2.p',d2_ordinal1)).

fof(f176,plain,(
    v1_ordinal1(sK0) ),
    inference(resolution,[],[f103,f118])).

fof(f118,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t10_wellord2.p',cc1_ordinal1)).

fof(f103,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,
    ( k1_wellord1(k1_wellord2(sK1),sK0) != sK0
    & r2_hidden(sK0,sK1)
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f45,f75,f74])).

fof(f74,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_wellord1(k1_wellord2(X1),X0) != X0
            & r2_hidden(X0,X1)
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( k1_wellord1(k1_wellord2(X1),sK0) != sK0
          & r2_hidden(sK0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) != X0
          & r2_hidden(X0,X1)
          & v3_ordinal1(X1) )
     => ( k1_wellord1(k1_wellord2(sK1),X0) != X0
        & r2_hidden(X0,sK1)
        & v3_ordinal1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) != X0
          & r2_hidden(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) != X0
          & r2_hidden(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
             => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t10_wellord2.p',t10_wellord2)).

fof(f228826,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | ~ r2_hidden(sK0,X2)
      | ~ r2_hidden(X2,X3) ) ),
    inference(subsumption_resolution,[],[f228708,f159])).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t10_wellord2.p',t5_subset)).

fof(f228708,plain,(
    ! [X2,X3] :
      ( v1_xboole_0(sK0)
      | ~ r2_hidden(sK0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f228705,f158])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t10_wellord2.p',t4_subset)).

fof(f228705,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | v1_xboole_0(sK0)
      | ~ r2_hidden(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f228703,f108])).

fof(f108,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t10_wellord2.p',dt_k1_wellord2)).

fof(f228703,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | v1_xboole_0(sK0)
      | ~ r2_hidden(sK0,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(superposition,[],[f228677,f170])).

fof(f170,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK5(X0,X1),sK6(X0,X1))
              | ~ r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1) )
            & ( r1_tarski(sK5(X0,X1),sK6(X0,X1))
              | r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1) )
            & r2_hidden(sK6(X0,X1),X0)
            & r2_hidden(sK5(X0,X1),X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f90,f91])).

fof(f91,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK5(X0,X1),sK6(X0,X1))
          | ~ r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1) )
        & ( r1_tarski(sK5(X0,X1),sK6(X0,X1))
          | r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1) )
        & r2_hidden(sK6(X0,X1),X0)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t10_wellord2.p',d1_wellord2)).

fof(f228677,plain,(
    ! [X4] :
      ( ~ m1_subset_1(k3_relat_1(k1_wellord2(X4)),sK0)
      | v1_xboole_0(sK0)
      | ~ r2_hidden(sK0,X4) ) ),
    inference(resolution,[],[f228635,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t10_wellord2.p',t2_subset)).

fof(f228635,plain,(
    ! [X3] :
      ( ~ r2_hidden(k3_relat_1(k1_wellord2(X3)),sK0)
      | ~ r2_hidden(sK0,X3) ) ),
    inference(resolution,[],[f228632,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t10_wellord2.p',antisymmetry_r2_hidden)).

fof(f228632,plain,(
    ! [X28] :
      ( r2_hidden(sK0,k3_relat_1(k1_wellord2(X28)))
      | ~ r2_hidden(sK0,X28) ) ),
    inference(subsumption_resolution,[],[f228618,f103])).

fof(f228618,plain,(
    ! [X28] :
      ( ~ v3_ordinal1(sK0)
      | ~ r2_hidden(sK0,X28)
      | r2_hidden(sK0,k3_relat_1(k1_wellord2(X28))) ) ),
    inference(duplicate_literal_removal,[],[f228556])).

fof(f228556,plain,(
    ! [X28] :
      ( ~ v3_ordinal1(sK0)
      | ~ r2_hidden(sK0,X28)
      | ~ r2_hidden(sK0,X28)
      | r2_hidden(sK0,k3_relat_1(k1_wellord2(X28)))
      | ~ v3_ordinal1(sK0) ) ),
    inference(resolution,[],[f34502,f174])).

fof(f174,plain,(
    ! [X0] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(condensation,[],[f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => r1_ordinal1(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t10_wellord2.p',reflexivity_r1_ordinal1)).

fof(f34502,plain,(
    ! [X8,X9] :
      ( ~ r1_ordinal1(X8,sK0)
      | ~ v3_ordinal1(X8)
      | ~ r2_hidden(sK0,X9)
      | ~ r2_hidden(X8,X9)
      | r2_hidden(X8,k3_relat_1(k1_wellord2(X9))) ) ),
    inference(subsumption_resolution,[],[f34472,f108])).

fof(f34472,plain,(
    ! [X8,X9] :
      ( ~ v3_ordinal1(X8)
      | ~ r1_ordinal1(X8,sK0)
      | ~ r2_hidden(sK0,X9)
      | ~ r2_hidden(X8,X9)
      | r2_hidden(X8,k3_relat_1(k1_wellord2(X9)))
      | ~ v1_relat_1(k1_wellord2(X9)) ) ),
    inference(resolution,[],[f969,f156])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t10_wellord2.p',t30_relat_1)).

fof(f969,plain,(
    ! [X8,X7] :
      ( r2_hidden(k4_tarski(X7,sK0),k1_wellord2(X8))
      | ~ v3_ordinal1(X7)
      | ~ r1_ordinal1(X7,sK0)
      | ~ r2_hidden(sK0,X8)
      | ~ r2_hidden(X7,X8) ) ),
    inference(subsumption_resolution,[],[f964,f108])).

fof(f964,plain,(
    ! [X8,X7] :
      ( ~ r1_ordinal1(X7,sK0)
      | ~ v3_ordinal1(X7)
      | r2_hidden(k4_tarski(X7,sK0),k1_wellord2(X8))
      | ~ r2_hidden(sK0,X8)
      | ~ r2_hidden(X7,X8)
      | ~ v1_relat_1(k1_wellord2(X8)) ) ),
    inference(resolution,[],[f180,f168])).

fof(f168,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f130])).

fof(f130,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f180,plain,(
    ! [X4] :
      ( r1_tarski(X4,sK0)
      | ~ r1_ordinal1(X4,sK0)
      | ~ v3_ordinal1(X4) ) ),
    inference(resolution,[],[f103,f141])).

fof(f141,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t10_wellord2.p',redefinition_r1_ordinal1)).

fof(f248009,plain,(
    r2_hidden(sK0,sK0) ),
    inference(forward_demodulation,[],[f248008,f247438])).

fof(f247438,plain,(
    sK0 = sK2(k1_wellord2(sK1),sK0,sK0) ),
    inference(subsumption_resolution,[],[f247437,f130403])).

fof(f130403,plain,
    ( sK0 = sK2(k1_wellord2(sK1),sK0,sK0)
    | ~ r2_hidden(sK2(k1_wellord2(sK1),sK0,sK0),sK0) ),
    inference(subsumption_resolution,[],[f130402,f226])).

fof(f226,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f207,f146])).

fof(f146,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f97,f98])).

fof(f98,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t10_wellord2.p',d3_tarski)).

fof(f207,plain,(
    r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f195,f184])).

fof(f184,plain,(
    v1_ordinal1(sK1) ),
    inference(resolution,[],[f104,f118])).

fof(f104,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f76])).

fof(f195,plain,
    ( r1_tarski(sK0,sK1)
    | ~ v1_ordinal1(sK1) ),
    inference(resolution,[],[f105,f121])).

fof(f105,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f76])).

fof(f130402,plain,
    ( ~ r2_hidden(sK2(k1_wellord2(sK1),sK0,sK0),sK1)
    | sK0 = sK2(k1_wellord2(sK1),sK0,sK0)
    | ~ r2_hidden(sK2(k1_wellord2(sK1),sK0,sK0),sK0) ),
    inference(subsumption_resolution,[],[f130401,f106])).

fof(f106,plain,(
    k1_wellord1(k1_wellord2(sK1),sK0) != sK0 ),
    inference(cnf_transformation,[],[f76])).

fof(f130401,plain,
    ( ~ r2_hidden(sK2(k1_wellord2(sK1),sK0,sK0),sK1)
    | k1_wellord1(k1_wellord2(sK1),sK0) = sK0
    | sK0 = sK2(k1_wellord2(sK1),sK0,sK0)
    | ~ r2_hidden(sK2(k1_wellord2(sK1),sK0,sK0),sK0) ),
    inference(duplicate_literal_removal,[],[f130362])).

fof(f130362,plain,
    ( ~ r2_hidden(sK2(k1_wellord2(sK1),sK0,sK0),sK1)
    | ~ r2_hidden(sK2(k1_wellord2(sK1),sK0,sK0),sK1)
    | k1_wellord1(k1_wellord2(sK1),sK0) = sK0
    | sK0 = sK2(k1_wellord2(sK1),sK0,sK0)
    | ~ r2_hidden(sK2(k1_wellord2(sK1),sK0,sK0),sK0) ),
    inference(resolution,[],[f39395,f1345])).

fof(f1345,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK2(k1_wellord2(sK1),sK0,X1),sK0)
      | ~ r2_hidden(sK2(k1_wellord2(sK1),sK0,X1),sK1)
      | k1_wellord1(k1_wellord2(sK1),sK0) = X1
      | sK0 = sK2(k1_wellord2(sK1),sK0,X1)
      | ~ r2_hidden(sK2(k1_wellord2(sK1),sK0,X1),X1) ) ),
    inference(subsumption_resolution,[],[f1328,f108])).

fof(f1328,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK2(k1_wellord2(sK1),sK0,X1),sK0)
      | ~ r2_hidden(sK2(k1_wellord2(sK1),sK0,X1),sK1)
      | k1_wellord1(k1_wellord2(sK1),sK0) = X1
      | sK0 = sK2(k1_wellord2(sK1),sK0,X1)
      | ~ r2_hidden(sK2(k1_wellord2(sK1),sK0,X1),X1)
      | ~ v1_relat_1(k1_wellord2(sK1)) ) ),
    inference(resolution,[],[f208,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( k1_wellord1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0)
      | sK2(X0,X1,X2) = X1
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0)
                | sK2(X0,X1,X2) = X1
                | ~ r2_hidden(sK2(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0)
                  & sK2(X0,X1,X2) != X1 )
                | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f79,f80])).

fof(f80,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0)
          | sK2(X0,X1,X2) = X1
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0)
            & sK2(X0,X1,X2) != X1 )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
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
    inference(rectify,[],[f78])).

fof(f78,plain,(
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
    inference(flattening,[],[f77])).

fof(f77,plain,(
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
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t10_wellord2.p',d1_wellord1)).

fof(f208,plain,(
    ! [X3] :
      ( r2_hidden(k4_tarski(X3,sK0),k1_wellord2(sK1))
      | ~ r1_tarski(X3,sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(subsumption_resolution,[],[f203,f108])).

fof(f203,plain,(
    ! [X3] :
      ( r2_hidden(k4_tarski(X3,sK0),k1_wellord2(sK1))
      | ~ r1_tarski(X3,sK0)
      | ~ r2_hidden(X3,sK1)
      | ~ v1_relat_1(k1_wellord2(sK1)) ) ),
    inference(resolution,[],[f105,f168])).

fof(f39395,plain,
    ( r1_tarski(sK2(k1_wellord2(sK1),sK0,sK0),sK0)
    | ~ r2_hidden(sK2(k1_wellord2(sK1),sK0,sK0),sK1) ),
    inference(subsumption_resolution,[],[f39372,f191])).

fof(f39372,plain,
    ( r2_hidden(sK2(k1_wellord2(sK1),sK0,sK0),sK0)
    | r1_tarski(sK2(k1_wellord2(sK1),sK0,sK0),sK0)
    | ~ r2_hidden(sK2(k1_wellord2(sK1),sK0,sK0),sK1) ),
    inference(resolution,[],[f3320,f210])).

fof(f210,plain,(
    ! [X5] :
      ( ~ r2_hidden(k4_tarski(X5,sK0),k1_wellord2(sK1))
      | r1_tarski(X5,sK0)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(subsumption_resolution,[],[f205,f108])).

fof(f205,plain,(
    ! [X5] :
      ( r1_tarski(X5,sK0)
      | ~ r2_hidden(k4_tarski(X5,sK0),k1_wellord2(sK1))
      | ~ r2_hidden(X5,sK1)
      | ~ v1_relat_1(k1_wellord2(sK1)) ) ),
    inference(resolution,[],[f105,f169])).

fof(f169,plain,(
    ! [X4,X0,X5] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f129])).

fof(f129,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f3320,plain,
    ( r2_hidden(k4_tarski(sK2(k1_wellord2(sK1),sK0,sK0),sK0),k1_wellord2(sK1))
    | r2_hidden(sK2(k1_wellord2(sK1),sK0,sK0),sK0) ),
    inference(equality_resolution,[],[f298])).

fof(f298,plain,(
    ! [X1] :
      ( sK0 != X1
      | r2_hidden(k4_tarski(sK2(k1_wellord2(sK1),sK0,X1),sK0),k1_wellord2(sK1))
      | r2_hidden(sK2(k1_wellord2(sK1),sK0,X1),X1) ) ),
    inference(subsumption_resolution,[],[f295,f108])).

fof(f295,plain,(
    ! [X1] :
      ( sK0 != X1
      | r2_hidden(k4_tarski(sK2(k1_wellord2(sK1),sK0,X1),sK0),k1_wellord2(sK1))
      | r2_hidden(sK2(k1_wellord2(sK1),sK0,X1),X1)
      | ~ v1_relat_1(k1_wellord2(sK1)) ) ),
    inference(superposition,[],[f106,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( k1_wellord1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f247437,plain,
    ( sK0 = sK2(k1_wellord2(sK1),sK0,sK0)
    | r2_hidden(sK2(k1_wellord2(sK1),sK0,sK0),sK0) ),
    inference(subsumption_resolution,[],[f247398,f247297])).

fof(f247297,plain,(
    v1_ordinal1(sK2(k1_wellord2(sK1),sK0,sK0)) ),
    inference(resolution,[],[f247247,f118])).

fof(f247247,plain,(
    v3_ordinal1(sK2(k1_wellord2(sK1),sK0,sK0)) ),
    inference(resolution,[],[f247245,f252])).

fof(f252,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | v3_ordinal1(X2) ) ),
    inference(resolution,[],[f185,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t10_wellord2.p',t1_subset)).

fof(f185,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,sK1)
      | v3_ordinal1(X1) ) ),
    inference(resolution,[],[f104,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_ordinal1(X1)
          | ~ m1_subset_1(X1,X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t10_wellord2.p',cc5_ordinal1)).

fof(f247245,plain,(
    r2_hidden(sK2(k1_wellord2(sK1),sK0,sK0),sK1) ),
    inference(subsumption_resolution,[],[f247244,f226])).

fof(f247244,plain,
    ( r2_hidden(sK2(k1_wellord2(sK1),sK0,sK0),sK1)
    | r2_hidden(sK2(k1_wellord2(sK1),sK0,sK0),sK0) ),
    inference(subsumption_resolution,[],[f247222,f108])).

fof(f247222,plain,
    ( r2_hidden(sK2(k1_wellord2(sK1),sK0,sK0),sK1)
    | r2_hidden(sK2(k1_wellord2(sK1),sK0,sK0),sK0)
    | ~ v1_relat_1(k1_wellord2(sK1)) ),
    inference(superposition,[],[f39396,f170])).

fof(f39396,plain,
    ( r2_hidden(sK2(k1_wellord2(sK1),sK0,sK0),k3_relat_1(k1_wellord2(sK1)))
    | r2_hidden(sK2(k1_wellord2(sK1),sK0,sK0),sK0) ),
    inference(subsumption_resolution,[],[f39375,f108])).

fof(f39375,plain,
    ( r2_hidden(sK2(k1_wellord2(sK1),sK0,sK0),sK0)
    | r2_hidden(sK2(k1_wellord2(sK1),sK0,sK0),k3_relat_1(k1_wellord2(sK1)))
    | ~ v1_relat_1(k1_wellord2(sK1)) ),
    inference(resolution,[],[f3320,f156])).

fof(f247398,plain,
    ( ~ v1_ordinal1(sK2(k1_wellord2(sK1),sK0,sK0))
    | sK0 = sK2(k1_wellord2(sK1),sK0,sK0)
    | r2_hidden(sK2(k1_wellord2(sK1),sK0,sK0),sK0) ),
    inference(resolution,[],[f247290,f712])).

fof(f712,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | ~ v1_ordinal1(X0)
      | sK0 = X0
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f175,f151])).

fof(f151,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t10_wellord2.p',d8_xboole_0)).

fof(f175,plain,(
    ! [X0] :
      ( ~ r2_xboole_0(X0,sK0)
      | r2_hidden(X0,sK0)
      | ~ v1_ordinal1(X0) ) ),
    inference(resolution,[],[f103,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_xboole_0(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t10_wellord2.p',t21_ordinal1)).

fof(f247290,plain,(
    r1_tarski(sK2(k1_wellord2(sK1),sK0,sK0),sK0) ),
    inference(subsumption_resolution,[],[f247289,f191])).

fof(f247289,plain,
    ( r1_tarski(sK2(k1_wellord2(sK1),sK0,sK0),sK0)
    | r2_hidden(sK2(k1_wellord2(sK1),sK0,sK0),sK0) ),
    inference(subsumption_resolution,[],[f247246,f106])).

fof(f247246,plain,
    ( r1_tarski(sK2(k1_wellord2(sK1),sK0,sK0),sK0)
    | k1_wellord1(k1_wellord2(sK1),sK0) = sK0
    | r2_hidden(sK2(k1_wellord2(sK1),sK0,sK0),sK0) ),
    inference(resolution,[],[f247245,f2174])).

fof(f2174,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK2(k1_wellord2(sK1),sK0,X2),sK1)
      | r1_tarski(sK2(k1_wellord2(sK1),sK0,X2),sK0)
      | k1_wellord1(k1_wellord2(sK1),sK0) = X2
      | r2_hidden(sK2(k1_wellord2(sK1),sK0,X2),X2) ) ),
    inference(subsumption_resolution,[],[f2166,f108])).

fof(f2166,plain,(
    ! [X2] :
      ( r1_tarski(sK2(k1_wellord2(sK1),sK0,X2),sK0)
      | ~ r2_hidden(sK2(k1_wellord2(sK1),sK0,X2),sK1)
      | k1_wellord1(k1_wellord2(sK1),sK0) = X2
      | r2_hidden(sK2(k1_wellord2(sK1),sK0,X2),X2)
      | ~ v1_relat_1(k1_wellord2(sK1)) ) ),
    inference(resolution,[],[f210,f115])).

fof(f248008,plain,(
    r2_hidden(sK2(k1_wellord2(sK1),sK0,sK0),sK0) ),
    inference(trivial_inequality_removal,[],[f248007])).

fof(f248007,plain,
    ( sK0 != sK0
    | r2_hidden(sK2(k1_wellord2(sK1),sK0,sK0),sK0) ),
    inference(duplicate_literal_removal,[],[f247989])).

fof(f247989,plain,
    ( sK0 != sK0
    | sK0 != sK0
    | r2_hidden(sK2(k1_wellord2(sK1),sK0,sK0),sK0) ),
    inference(superposition,[],[f297,f247438])).

fof(f297,plain,(
    ! [X0] :
      ( sK0 != sK2(k1_wellord2(sK1),sK0,X0)
      | sK0 != X0
      | r2_hidden(sK2(k1_wellord2(sK1),sK0,X0),X0) ) ),
    inference(subsumption_resolution,[],[f294,f108])).

fof(f294,plain,(
    ! [X0] :
      ( sK0 != X0
      | sK0 != sK2(k1_wellord2(sK1),sK0,X0)
      | r2_hidden(sK2(k1_wellord2(sK1),sK0,X0),X0)
      | ~ v1_relat_1(k1_wellord2(sK1)) ) ),
    inference(superposition,[],[f106,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( k1_wellord1(X0,X1) = X2
      | sK2(X0,X1,X2) != X1
      | r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f81])).
%------------------------------------------------------------------------------
