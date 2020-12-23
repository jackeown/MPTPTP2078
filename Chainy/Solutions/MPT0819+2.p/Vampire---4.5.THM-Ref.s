%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0819+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:49 EST 2020

% Result     : Theorem 1.98s
% Output     : Refutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   27 (  47 expanded)
%              Number of leaves         :    5 (  12 expanded)
%              Depth                    :   10
%              Number of atoms          :   73 ( 163 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7227,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f3293,f3294,f7169,f5153])).

fof(f5153,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2434])).

fof(f2434,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f2433])).

fof(f2433,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f335])).

fof(f335,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).

fof(f7169,plain,(
    ~ r1_tarski(k2_zfmisc_1(sK7,sK9),k2_zfmisc_1(sK8,sK10)) ),
    inference(resolution,[],[f7165,f3292])).

fof(f3292,plain,(
    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK7,sK9))) ),
    inference(cnf_transformation,[],[f2488])).

fof(f2488,plain,
    ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK8,sK10)))
    & r1_tarski(sK9,sK10)
    & r1_tarski(sK7,sK8)
    & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK7,sK9))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10,sK11])],[f1251,f2487])).

fof(f2487,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
   => ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK8,sK10)))
      & r1_tarski(sK9,sK10)
      & r1_tarski(sK7,sK8)
      & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK7,sK9))) ) ),
    introduced(choice_axiom,[])).

fof(f1251,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1)
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f1250])).

fof(f1250,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1)
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f1218])).

fof(f1218,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => ( ( r1_tarski(X2,X3)
            & r1_tarski(X0,X1) )
         => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ),
    inference(negated_conjecture,[],[f1217])).

fof(f1217,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_relset_1)).

fof(f7165,plain,(
    ! [X3] :
      ( ~ m1_subset_1(sK11,k1_zfmisc_1(X3))
      | ~ r1_tarski(X3,k2_zfmisc_1(sK8,sK10)) ) ),
    inference(resolution,[],[f7142,f4615])).

fof(f4615,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3044])).

fof(f3044,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f7142,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK11,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(sK8,sK10)) ) ),
    inference(resolution,[],[f4935,f7127])).

fof(f7127,plain,(
    ~ r1_tarski(sK11,k2_zfmisc_1(sK8,sK10)) ),
    inference(resolution,[],[f4616,f3295])).

fof(f3295,plain,(
    ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK8,sK10))) ),
    inference(cnf_transformation,[],[f2488])).

fof(f4616,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3044])).

fof(f4935,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2345])).

fof(f2345,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f2344])).

fof(f2344,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f3294,plain,(
    r1_tarski(sK9,sK10) ),
    inference(cnf_transformation,[],[f2488])).

fof(f3293,plain,(
    r1_tarski(sK7,sK8) ),
    inference(cnf_transformation,[],[f2488])).
%------------------------------------------------------------------------------
