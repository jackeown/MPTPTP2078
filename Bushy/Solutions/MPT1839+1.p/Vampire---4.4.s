%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t2_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:30 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  107 (1617 expanded)
%              Number of leaves         :   16 ( 470 expanded)
%              Depth                    :   34
%              Number of atoms          :  259 (5621 expanded)
%              Number of equality atoms :   36 ( 532 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1039,plain,(
    $false ),
    inference(resolution,[],[f1036,f789])).

fof(f789,plain,(
    r1_tarski(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f778,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t2_tex_2.p',t3_subset)).

fof(f778,plain,(
    m1_subset_1(sK0,k1_zfmisc_1(k3_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f777,f767])).

fof(f767,plain,(
    k6_domain_1(k3_xboole_0(sK0,sK1),sK3(sK0)) = sK0 ),
    inference(forward_demodulation,[],[f766,f98])).

fof(f98,plain,(
    k1_tarski(sK3(sK0)) = sK0 ),
    inference(forward_demodulation,[],[f97,f85])).

fof(f85,plain,(
    k6_domain_1(sK0,sK3(sK0)) = sK0 ),
    inference(subsumption_resolution,[],[f82,f58])).

fof(f58,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ~ r1_tarski(sK0,sK1)
    & ~ v1_xboole_0(k3_xboole_0(sK0,sK1))
    & v1_zfmisc_1(sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f46,f45])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(X0,X1)
            & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
        & v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(sK0,X1)
          & ~ v1_xboole_0(k3_xboole_0(sK0,X1)) )
      & v1_zfmisc_1(sK0)
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
     => ( ~ r1_tarski(X0,sK1)
        & ~ v1_xboole_0(k3_xboole_0(X0,sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_zfmisc_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
           => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
         => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t2_tex_2.p',t2_tex_2)).

fof(f82,plain,
    ( k6_domain_1(sK0,sK3(sK0)) = sK0
    | ~ v1_zfmisc_1(sK0) ),
    inference(resolution,[],[f57,f67])).

fof(f67,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK3(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK3(X0)) = X0
            & m1_subset_1(sK3(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f51,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK3(X0)) = X0
        & m1_subset_1(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t2_tex_2.p',d1_tex_2)).

fof(f57,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f97,plain,(
    k6_domain_1(sK0,sK3(sK0)) = k1_tarski(sK3(sK0)) ),
    inference(subsumption_resolution,[],[f94,f57])).

fof(f94,plain,
    ( k6_domain_1(sK0,sK3(sK0)) = k1_tarski(sK3(sK0))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f84,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t2_tex_2.p',redefinition_k6_domain_1)).

fof(f84,plain,(
    m1_subset_1(sK3(sK0),sK0) ),
    inference(subsumption_resolution,[],[f81,f58])).

fof(f81,plain,
    ( m1_subset_1(sK3(sK0),sK0)
    | ~ v1_zfmisc_1(sK0) ),
    inference(resolution,[],[f57,f66])).

fof(f66,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f766,plain,(
    k6_domain_1(k3_xboole_0(sK0,sK1),sK3(sK0)) = k1_tarski(sK3(sK0)) ),
    inference(backward_demodulation,[],[f765,f327])).

fof(f327,plain,(
    k6_domain_1(k3_xboole_0(sK0,sK1),sK4(k3_xboole_0(sK0,sK1))) = k1_tarski(sK4(k3_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f89,f72])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t2_tex_2.p',existence_m1_subset_1)).

fof(f89,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k3_xboole_0(sK0,sK1))
      | k6_domain_1(k3_xboole_0(sK0,sK1),X0) = k1_tarski(X0) ) ),
    inference(resolution,[],[f59,f71])).

fof(f59,plain,(
    ~ v1_xboole_0(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f47])).

fof(f765,plain,(
    sK3(sK0) = sK4(k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f758,f72])).

fof(f758,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k3_xboole_0(sK0,sK1))
      | sK3(sK0) = X0 ) ),
    inference(subsumption_resolution,[],[f754,f61])).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t2_tex_2.p',t17_xboole_1)).

fof(f754,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k3_xboole_0(sK0,sK1))
      | sK3(sK0) = X0
      | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0) ) ),
    inference(resolution,[],[f749,f603])).

fof(f603,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | sK3(sK0) = X0
      | ~ r1_tarski(X1,sK0) ) ),
    inference(resolution,[],[f237,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f237,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X1,X2)
      | sK3(sK0) = X1 ) ),
    inference(resolution,[],[f214,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t2_tex_2.p',t4_subset)).

fof(f214,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | sK3(sK0) = X0 ) ),
    inference(resolution,[],[f110,f200])).

fof(f200,plain,(
    ! [X0] :
      ( r1_tarski(k1_tarski(X0),sK0)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f199,f57])).

fof(f199,plain,(
    ! [X0] :
      ( r1_tarski(k1_tarski(X0),sK0)
      | ~ m1_subset_1(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f198])).

fof(f198,plain,(
    ! [X0] :
      ( r1_tarski(k1_tarski(X0),sK0)
      | ~ m1_subset_1(X0,sK0)
      | ~ m1_subset_1(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(superposition,[],[f175,f71])).

fof(f175,plain,(
    ! [X0] :
      ( r1_tarski(k6_domain_1(sK0,X0),sK0)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(resolution,[],[f80,f75])).

fof(f80,plain,(
    ! [X1] :
      ( m1_subset_1(k6_domain_1(sK0,X1),k1_zfmisc_1(sK0))
      | ~ m1_subset_1(X1,sK0) ) ),
    inference(resolution,[],[f57,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t2_tex_2.p',dt_k6_domain_1)).

fof(f110,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tarski(X0),sK0)
      | sK3(sK0) = X0 ) ),
    inference(superposition,[],[f78,f98])).

fof(f78,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t2_tex_2.p',t24_zfmisc_1)).

fof(f749,plain,(
    ! [X0] :
      ( r2_hidden(X0,k3_xboole_0(sK0,sK1))
      | ~ m1_subset_1(X0,k3_xboole_0(sK0,sK1)) ) ),
    inference(resolution,[],[f742,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
     => r2_hidden(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t2_tex_2.p',t37_zfmisc_1)).

fof(f742,plain,(
    ! [X2] :
      ( r1_tarski(k1_tarski(X2),k3_xboole_0(sK0,sK1))
      | ~ m1_subset_1(X2,k3_xboole_0(sK0,sK1)) ) ),
    inference(resolution,[],[f413,f75])).

fof(f413,plain,(
    ! [X0] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(k3_xboole_0(sK0,sK1)))
      | ~ m1_subset_1(X0,k3_xboole_0(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f410,f59])).

fof(f410,plain,(
    ! [X0] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(k3_xboole_0(sK0,sK1)))
      | ~ m1_subset_1(X0,k3_xboole_0(sK0,sK1))
      | v1_xboole_0(k3_xboole_0(sK0,sK1)) ) ),
    inference(duplicate_literal_removal,[],[f409])).

fof(f409,plain,(
    ! [X0] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(k3_xboole_0(sK0,sK1)))
      | ~ m1_subset_1(X0,k3_xboole_0(sK0,sK1))
      | ~ m1_subset_1(X0,k3_xboole_0(sK0,sK1))
      | v1_xboole_0(k3_xboole_0(sK0,sK1)) ) ),
    inference(superposition,[],[f90,f71])).

fof(f90,plain,(
    ! [X1] :
      ( m1_subset_1(k6_domain_1(k3_xboole_0(sK0,sK1),X1),k1_zfmisc_1(k3_xboole_0(sK0,sK1)))
      | ~ m1_subset_1(X1,k3_xboole_0(sK0,sK1)) ) ),
    inference(resolution,[],[f59,f70])).

fof(f777,plain,(
    m1_subset_1(k6_domain_1(k3_xboole_0(sK0,sK1),sK3(sK0)),k1_zfmisc_1(k3_xboole_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f772,f59])).

fof(f772,plain,
    ( m1_subset_1(k6_domain_1(k3_xboole_0(sK0,sK1),sK3(sK0)),k1_zfmisc_1(k3_xboole_0(sK0,sK1)))
    | v1_xboole_0(k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f768,f70])).

fof(f768,plain,(
    m1_subset_1(sK3(sK0),k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f72,f765])).

fof(f1036,plain,(
    ! [X0] : ~ r1_tarski(sK0,k3_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f1025,f62])).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t2_tex_2.p',commutativity_k3_xboole_0)).

fof(f1025,plain,(
    ! [X2] : ~ r1_tarski(sK0,k3_xboole_0(sK1,X2)) ),
    inference(resolution,[],[f1003,f61])).

fof(f1003,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,X0)
      | ~ r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f982,f76])).

fof(f982,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
      | ~ r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f981,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(sK0),X1)
      | ~ r1_tarski(sK0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f112,f74])).

fof(f112,plain,(
    ! [X2] :
      ( r2_hidden(sK3(sK0),X2)
      | ~ r1_tarski(sK0,X2) ) ),
    inference(superposition,[],[f77,f98])).

fof(f981,plain,(
    ~ m1_subset_1(sK3(sK0),sK1) ),
    inference(subsumption_resolution,[],[f980,f60])).

fof(f60,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f980,plain,
    ( r1_tarski(sK0,sK1)
    | ~ m1_subset_1(sK3(sK0),sK1) ),
    inference(superposition,[],[f975,f98])).

fof(f975,plain,(
    ! [X0] :
      ( r1_tarski(k1_tarski(X0),sK1)
      | ~ m1_subset_1(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f974,f781])).

fof(f781,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(resolution,[],[f778,f329])).

fof(f329,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k3_xboole_0(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f320,f75])).

fof(f320,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK0,k3_xboole_0(X1,X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f313,f62])).

fof(f313,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(sK0,k3_xboole_0(X2,X3))
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f299,f61])).

fof(f299,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK0,X1)
      | ~ r1_tarski(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f124,f76])).

fof(f124,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | ~ v1_xboole_0(X3)
      | ~ r1_tarski(sK0,X2) ) ),
    inference(resolution,[],[f112,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t2_tex_2.p',t5_subset)).

fof(f974,plain,(
    ! [X0] :
      ( r1_tarski(k1_tarski(X0),sK1)
      | ~ m1_subset_1(X0,sK1)
      | v1_xboole_0(sK1) ) ),
    inference(duplicate_literal_removal,[],[f973])).

fof(f973,plain,(
    ! [X0] :
      ( r1_tarski(k1_tarski(X0),sK1)
      | ~ m1_subset_1(X0,sK1)
      | ~ m1_subset_1(X0,sK1)
      | v1_xboole_0(sK1) ) ),
    inference(superposition,[],[f942,f71])).

fof(f942,plain,(
    ! [X2] :
      ( r1_tarski(k6_domain_1(sK1,X2),sK1)
      | ~ m1_subset_1(X2,sK1) ) ),
    inference(resolution,[],[f796,f75])).

fof(f796,plain,(
    ! [X1] :
      ( m1_subset_1(k6_domain_1(sK1,X1),k1_zfmisc_1(sK1))
      | ~ m1_subset_1(X1,sK1) ) ),
    inference(resolution,[],[f781,f70])).
%------------------------------------------------------------------------------
