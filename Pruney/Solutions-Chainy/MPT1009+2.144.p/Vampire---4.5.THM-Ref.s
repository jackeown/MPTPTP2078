%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  103 (1144 expanded)
%              Number of leaves         :   13 ( 279 expanded)
%              Depth                    :   22
%              Number of atoms          :  344 (5379 expanded)
%              Number of equality atoms :   81 (1379 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f282,plain,(
    $false ),
    inference(resolution,[],[f268,f138])).

fof(f138,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f136,f119])).

fof(f119,plain,(
    ! [X0] : k7_relset_1(k1_tarski(sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(resolution,[],[f46,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK3,k1_tarski(sK0),sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f38])).

fof(f38,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK3,k1_tarski(sK0),sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

fof(f136,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k2_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f48,f134])).

fof(f134,plain,(
    k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) ),
    inference(backward_demodulation,[],[f104,f115])).

fof(f115,plain,(
    k2_relat_1(sK3) = k2_relset_1(k1_tarski(sK0),sK1,sK3) ),
    inference(resolution,[],[f46,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f104,plain,(
    k1_tarski(k1_funct_1(sK3,sK0)) = k2_relset_1(k1_tarski(sK0),sK1,sK3) ),
    inference(subsumption_resolution,[],[f103,f44])).

fof(f44,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f103,plain,
    ( k1_tarski(k1_funct_1(sK3,sK0)) = k2_relset_1(k1_tarski(sK0),sK1,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f102,f46])).

fof(f102,plain,
    ( k1_tarski(k1_funct_1(sK3,sK0)) = k2_relset_1(k1_tarski(sK0),sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f98,f47])).

fof(f47,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f39])).

fof(f98,plain,
    ( k1_tarski(k1_funct_1(sK3,sK0)) = k2_relset_1(k1_tarski(sK0),sK1,sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f45,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      | ~ v1_funct_2(X2,k1_tarski(X0),X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      | ~ v1_funct_2(X2,k1_tarski(X0),X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      | ~ v1_funct_2(X2,k1_tarski(X0),X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

fof(f45,plain,(
    v1_funct_2(sK3,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f48,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f268,plain,(
    ! [X1] : r1_tarski(k9_relat_1(sK3,X1),k2_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f267,f258])).

fof(f258,plain,(
    ! [X0] : k9_relat_1(sK3,X0) = k7_relset_1(k1_tarski(sK0),k2_relat_1(sK3),sK3,X0) ),
    inference(resolution,[],[f244,f75])).

fof(f244,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_relat_1(sK3)))) ),
    inference(subsumption_resolution,[],[f243,f164])).

fof(f164,plain,(
    ! [X5] :
      ( r2_hidden(sK4(k1_tarski(sK0),X5,sK3),k1_tarski(sK0))
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),X5))) ) ),
    inference(forward_demodulation,[],[f163,f123])).

fof(f123,plain,(
    k1_tarski(sK0) = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f114,f112])).

fof(f112,plain,(
    k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK3) ),
    inference(subsumption_resolution,[],[f111,f46])).

fof(f111,plain,
    ( k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f101,f47])).

fof(f101,plain,
    ( k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(resolution,[],[f45,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f114,plain,(
    k1_relat_1(sK3) = k1_relset_1(k1_tarski(sK0),sK1,sK3) ),
    inference(resolution,[],[f46,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f163,plain,(
    ! [X5] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),X5)))
      | r2_hidden(sK4(k1_relat_1(sK3),X5,sK3),k1_relat_1(sK3)) ) ),
    inference(forward_demodulation,[],[f162,f123])).

fof(f162,plain,(
    ! [X5] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X5)))
      | r2_hidden(sK4(k1_relat_1(sK3),X5,sK3),k1_relat_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f152,f44])).

fof(f152,plain,(
    ! [X5] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X5)))
      | r2_hidden(sK4(k1_relat_1(sK3),X5,sK3),k1_relat_1(sK3))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f146,f84])).

fof(f84,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

fof(f146,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f122,f51])).

fof(f51,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f122,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski(sK0),sK1)) ),
    inference(resolution,[],[f46,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f243,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_relat_1(sK3))))
    | ~ r2_hidden(sK4(k1_tarski(sK0),k2_relat_1(sK3),sK3),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f242,f123])).

fof(f242,plain,
    ( ~ r2_hidden(sK4(k1_tarski(sK0),k2_relat_1(sK3),sK3),k1_tarski(sK0))
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) ),
    inference(forward_demodulation,[],[f241,f123])).

fof(f241,plain,
    ( ~ r2_hidden(sK4(k1_relat_1(sK3),k2_relat_1(sK3),sK3),k1_tarski(sK0))
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) ),
    inference(subsumption_resolution,[],[f240,f146])).

fof(f240,plain,
    ( ~ r2_hidden(sK4(k1_relat_1(sK3),k2_relat_1(sK3),sK3),k1_tarski(sK0))
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f233,f44])).

fof(f233,plain,
    ( ~ r2_hidden(sK4(k1_relat_1(sK3),k2_relat_1(sK3),sK3),k1_tarski(sK0))
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f135,f83])).

fof(f83,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK4(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f135,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
      | ~ r2_hidden(X0,k1_tarski(sK0)) ) ),
    inference(backward_demodulation,[],[f108,f134])).

fof(f108,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK3,X0),k1_tarski(k1_funct_1(sK3,sK0)))
      | ~ r2_hidden(X0,k1_tarski(sK0)) ) ),
    inference(forward_demodulation,[],[f107,f104])).

fof(f107,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k1_tarski(sK0),sK1,sK3))
      | ~ r2_hidden(X0,k1_tarski(sK0)) ) ),
    inference(subsumption_resolution,[],[f106,f44])).

fof(f106,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k1_tarski(sK0),sK1,sK3))
      | ~ r2_hidden(X0,k1_tarski(sK0))
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f105,f46])).

fof(f105,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k1_tarski(sK0),sK1,sK3))
      | ~ r2_hidden(X0,k1_tarski(sK0))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f99,f47])).

fof(f99,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k1_tarski(sK0),sK1,sK3))
      | k1_xboole_0 = sK1
      | ~ r2_hidden(X0,k1_tarski(sK0))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f45,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f36])).

% (16904)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

fof(f267,plain,(
    ! [X1] : r1_tarski(k7_relset_1(k1_tarski(sK0),k2_relat_1(sK3),sK3,X1),k2_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f266,f44])).

fof(f266,plain,(
    ! [X1] :
      ( r1_tarski(k7_relset_1(k1_tarski(sK0),k2_relat_1(sK3),sK3,X1),k2_relat_1(sK3))
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f259,f239])).

fof(f239,plain,(
    v1_funct_2(sK3,k1_tarski(sK0),k2_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f238,f170])).

fof(f170,plain,(
    ! [X7] :
      ( r2_hidden(sK4(k1_tarski(sK0),X7,sK3),k1_tarski(sK0))
      | v1_funct_2(sK3,k1_tarski(sK0),X7) ) ),
    inference(forward_demodulation,[],[f169,f123])).

fof(f169,plain,(
    ! [X7] :
      ( v1_funct_2(sK3,k1_tarski(sK0),X7)
      | r2_hidden(sK4(k1_relat_1(sK3),X7,sK3),k1_relat_1(sK3)) ) ),
    inference(forward_demodulation,[],[f168,f123])).

fof(f168,plain,(
    ! [X7] :
      ( v1_funct_2(sK3,k1_relat_1(sK3),X7)
      | r2_hidden(sK4(k1_relat_1(sK3),X7,sK3),k1_relat_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f154,f44])).

fof(f154,plain,(
    ! [X7] :
      ( v1_funct_2(sK3,k1_relat_1(sK3),X7)
      | r2_hidden(sK4(k1_relat_1(sK3),X7,sK3),k1_relat_1(sK3))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f146,f86])).

fof(f86,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f238,plain,
    ( v1_funct_2(sK3,k1_tarski(sK0),k2_relat_1(sK3))
    | ~ r2_hidden(sK4(k1_tarski(sK0),k2_relat_1(sK3),sK3),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f237,f123])).

fof(f237,plain,
    ( ~ r2_hidden(sK4(k1_tarski(sK0),k2_relat_1(sK3),sK3),k1_tarski(sK0))
    | v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f236,f123])).

fof(f236,plain,
    ( ~ r2_hidden(sK4(k1_relat_1(sK3),k2_relat_1(sK3),sK3),k1_tarski(sK0))
    | v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f235,f146])).

fof(f235,plain,
    ( ~ r2_hidden(sK4(k1_relat_1(sK3),k2_relat_1(sK3),sK3),k1_tarski(sK0))
    | v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f232,f44])).

fof(f232,plain,
    ( ~ r2_hidden(sK4(k1_relat_1(sK3),k2_relat_1(sK3),sK3),k1_tarski(sK0))
    | v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f135,f85])).

fof(f85,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | ~ r2_hidden(k1_funct_1(X2,sK4(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f259,plain,(
    ! [X1] :
      ( r1_tarski(k7_relset_1(k1_tarski(sK0),k2_relat_1(sK3),sK3,X1),k2_relat_1(sK3))
      | ~ v1_funct_2(sK3,k1_tarski(sK0),k2_relat_1(sK3))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f244,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k7_relset_1(X0,X1,X3,X2),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k7_relset_1(X0,X1,X3,X2),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k7_relset_1(X0,X1,X3,X2),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:02:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (16924)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (16916)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (16908)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (16924)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f282,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(resolution,[],[f268,f138])).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))),
% 0.21/0.52    inference(backward_demodulation,[],[f136,f119])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    ( ! [X0] : (k7_relset_1(k1_tarski(sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 0.21/0.52    inference(resolution,[],[f46,f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 0.21/0.52    inference(flattening,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 0.21/0.52    inference(ennf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.21/0.52    inference(negated_conjecture,[],[f16])).
% 0.21/0.52  fof(f16,conjecture,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k2_relat_1(sK3))),
% 0.21/0.52    inference(backward_demodulation,[],[f48,f134])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)),
% 0.21/0.52    inference(backward_demodulation,[],[f104,f115])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    k2_relat_1(sK3) = k2_relset_1(k1_tarski(sK0),sK1,sK3)),
% 0.21/0.52    inference(resolution,[],[f46,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    k1_tarski(k1_funct_1(sK3,sK0)) = k2_relset_1(k1_tarski(sK0),sK1,sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f103,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    v1_funct_1(sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    k1_tarski(k1_funct_1(sK3,sK0)) = k2_relset_1(k1_tarski(sK0),sK1,sK3) | ~v1_funct_1(sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f102,f46])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    k1_tarski(k1_funct_1(sK3,sK0)) = k2_relset_1(k1_tarski(sK0),sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | ~v1_funct_1(sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f98,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    k1_xboole_0 != sK1),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    k1_tarski(k1_funct_1(sK3,sK0)) = k2_relset_1(k1_tarski(sK0),sK1,sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | ~v1_funct_1(sK3)),
% 0.21/0.52    inference(resolution,[],[f45,f74])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) | ~v1_funct_2(X2,k1_tarski(X0),X1) | ~v1_funct_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) | ~v1_funct_2(X2,k1_tarski(X0),X1) | ~v1_funct_1(X2))),
% 0.21/0.52    inference(flattening,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) | k1_xboole_0 = X1) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) | ~v1_funct_2(X2,k1_tarski(X0),X1) | ~v1_funct_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    v1_funct_2(sK3,k1_tarski(sK0),sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f268,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(k9_relat_1(sK3,X1),k2_relat_1(sK3))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f267,f258])).
% 0.21/0.52  fof(f258,plain,(
% 0.21/0.52    ( ! [X0] : (k9_relat_1(sK3,X0) = k7_relset_1(k1_tarski(sK0),k2_relat_1(sK3),sK3,X0)) )),
% 0.21/0.52    inference(resolution,[],[f244,f75])).
% 0.21/0.52  fof(f244,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_relat_1(sK3))))),
% 0.21/0.52    inference(subsumption_resolution,[],[f243,f164])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    ( ! [X5] : (r2_hidden(sK4(k1_tarski(sK0),X5,sK3),k1_tarski(sK0)) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),X5)))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f163,f123])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    k1_tarski(sK0) = k1_relat_1(sK3)),
% 0.21/0.52    inference(forward_demodulation,[],[f114,f112])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f111,f46])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f101,f47])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.21/0.52    inference(resolution,[],[f45,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(flattening,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    k1_relat_1(sK3) = k1_relset_1(k1_tarski(sK0),sK1,sK3)),
% 0.21/0.52    inference(resolution,[],[f46,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    ( ! [X5] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),X5))) | r2_hidden(sK4(k1_relat_1(sK3),X5,sK3),k1_relat_1(sK3))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f162,f123])).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    ( ! [X5] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X5))) | r2_hidden(sK4(k1_relat_1(sK3),X5,sK3),k1_relat_1(sK3))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f152,f44])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    ( ! [X5] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X5))) | r2_hidden(sK4(k1_relat_1(sK3),X5,sK3),k1_relat_1(sK3)) | ~v1_funct_1(sK3)) )),
% 0.21/0.52    inference(resolution,[],[f146,f84])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(equality_resolution,[],[f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK4(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1) & r2_hidden(sK4(X0,X1,X2),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(flattening,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    v1_relat_1(sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f122,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(k1_tarski(sK0),sK1))),
% 0.21/0.52    inference(resolution,[],[f46,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.52  fof(f243,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_relat_1(sK3)))) | ~r2_hidden(sK4(k1_tarski(sK0),k2_relat_1(sK3),sK3),k1_tarski(sK0))),
% 0.21/0.52    inference(forward_demodulation,[],[f242,f123])).
% 0.21/0.52  fof(f242,plain,(
% 0.21/0.52    ~r2_hidden(sK4(k1_tarski(sK0),k2_relat_1(sK3),sK3),k1_tarski(sK0)) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))),
% 0.21/0.52    inference(forward_demodulation,[],[f241,f123])).
% 0.21/0.52  fof(f241,plain,(
% 0.21/0.52    ~r2_hidden(sK4(k1_relat_1(sK3),k2_relat_1(sK3),sK3),k1_tarski(sK0)) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))),
% 0.21/0.52    inference(subsumption_resolution,[],[f240,f146])).
% 0.21/0.52  fof(f240,plain,(
% 0.21/0.52    ~r2_hidden(sK4(k1_relat_1(sK3),k2_relat_1(sK3),sK3),k1_tarski(sK0)) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~v1_relat_1(sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f233,f44])).
% 0.21/0.52  fof(f233,plain,(
% 0.21/0.52    ~r2_hidden(sK4(k1_relat_1(sK3),k2_relat_1(sK3),sK3),k1_tarski(sK0)) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.52    inference(resolution,[],[f135,f83])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~r2_hidden(k1_funct_1(X2,sK4(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(equality_resolution,[],[f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f43])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) | ~r2_hidden(X0,k1_tarski(sK0))) )),
% 0.21/0.52    inference(backward_demodulation,[],[f108,f134])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),k1_tarski(k1_funct_1(sK3,sK0))) | ~r2_hidden(X0,k1_tarski(sK0))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f107,f104])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k1_tarski(sK0),sK1,sK3)) | ~r2_hidden(X0,k1_tarski(sK0))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f106,f44])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k1_tarski(sK0),sK1,sK3)) | ~r2_hidden(X0,k1_tarski(sK0)) | ~v1_funct_1(sK3)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f105,f46])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k1_tarski(sK0),sK1,sK3)) | ~r2_hidden(X0,k1_tarski(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | ~v1_funct_1(sK3)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f99,f47])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k1_tarski(sK0),sK1,sK3)) | k1_xboole_0 = sK1 | ~r2_hidden(X0,k1_tarski(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | ~v1_funct_1(sK3)) )),
% 0.21/0.52    inference(resolution,[],[f45,f77])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.52    inference(flattening,[],[f36])).
% 0.21/0.52  % (16904)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.52    inference(ennf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).
% 0.21/0.52  fof(f267,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(k7_relset_1(k1_tarski(sK0),k2_relat_1(sK3),sK3,X1),k2_relat_1(sK3))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f266,f44])).
% 0.21/0.52  fof(f266,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(k7_relset_1(k1_tarski(sK0),k2_relat_1(sK3),sK3,X1),k2_relat_1(sK3)) | ~v1_funct_1(sK3)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f259,f239])).
% 0.21/0.52  fof(f239,plain,(
% 0.21/0.52    v1_funct_2(sK3,k1_tarski(sK0),k2_relat_1(sK3))),
% 0.21/0.52    inference(subsumption_resolution,[],[f238,f170])).
% 0.21/0.52  fof(f170,plain,(
% 0.21/0.52    ( ! [X7] : (r2_hidden(sK4(k1_tarski(sK0),X7,sK3),k1_tarski(sK0)) | v1_funct_2(sK3,k1_tarski(sK0),X7)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f169,f123])).
% 0.21/0.52  fof(f169,plain,(
% 0.21/0.52    ( ! [X7] : (v1_funct_2(sK3,k1_tarski(sK0),X7) | r2_hidden(sK4(k1_relat_1(sK3),X7,sK3),k1_relat_1(sK3))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f168,f123])).
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    ( ! [X7] : (v1_funct_2(sK3,k1_relat_1(sK3),X7) | r2_hidden(sK4(k1_relat_1(sK3),X7,sK3),k1_relat_1(sK3))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f154,f44])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    ( ! [X7] : (v1_funct_2(sK3,k1_relat_1(sK3),X7) | r2_hidden(sK4(k1_relat_1(sK3),X7,sK3),k1_relat_1(sK3)) | ~v1_funct_1(sK3)) )),
% 0.21/0.52    inference(resolution,[],[f146,f86])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(equality_resolution,[],[f70])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | r2_hidden(sK4(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f43])).
% 0.21/0.52  fof(f238,plain,(
% 0.21/0.52    v1_funct_2(sK3,k1_tarski(sK0),k2_relat_1(sK3)) | ~r2_hidden(sK4(k1_tarski(sK0),k2_relat_1(sK3),sK3),k1_tarski(sK0))),
% 0.21/0.52    inference(forward_demodulation,[],[f237,f123])).
% 0.21/0.52  fof(f237,plain,(
% 0.21/0.52    ~r2_hidden(sK4(k1_tarski(sK0),k2_relat_1(sK3),sK3),k1_tarski(sK0)) | v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))),
% 0.21/0.52    inference(forward_demodulation,[],[f236,f123])).
% 0.21/0.52  fof(f236,plain,(
% 0.21/0.52    ~r2_hidden(sK4(k1_relat_1(sK3),k2_relat_1(sK3),sK3),k1_tarski(sK0)) | v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))),
% 0.21/0.52    inference(subsumption_resolution,[],[f235,f146])).
% 0.21/0.52  fof(f235,plain,(
% 0.21/0.52    ~r2_hidden(sK4(k1_relat_1(sK3),k2_relat_1(sK3),sK3),k1_tarski(sK0)) | v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f232,f44])).
% 0.21/0.52  fof(f232,plain,(
% 0.21/0.52    ~r2_hidden(sK4(k1_relat_1(sK3),k2_relat_1(sK3),sK3),k1_tarski(sK0)) | v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.52    inference(resolution,[],[f135,f85])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | ~r2_hidden(k1_funct_1(X2,sK4(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(equality_resolution,[],[f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f43])).
% 0.21/0.52  fof(f259,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(k7_relset_1(k1_tarski(sK0),k2_relat_1(sK3),sK3,X1),k2_relat_1(sK3)) | ~v1_funct_2(sK3,k1_tarski(sK0),k2_relat_1(sK3)) | ~v1_funct_1(sK3)) )),
% 0.21/0.52    inference(resolution,[],[f244,f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.52    inference(flattening,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_2)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (16924)------------------------------
% 0.21/0.52  % (16924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (16924)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (16924)Memory used [KB]: 1791
% 0.21/0.52  % (16924)Time elapsed: 0.062 s
% 0.21/0.52  % (16924)------------------------------
% 0.21/0.52  % (16924)------------------------------
% 0.21/0.52  % (16907)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (16904)Refutation not found, incomplete strategy% (16904)------------------------------
% 0.21/0.52  % (16904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (16904)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (16904)Memory used [KB]: 6396
% 0.21/0.52  % (16904)Time elapsed: 0.114 s
% 0.21/0.52  % (16904)------------------------------
% 0.21/0.52  % (16904)------------------------------
% 0.21/0.52  % (16905)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (16896)Success in time 0.155 s
%------------------------------------------------------------------------------
