%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1002+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:02 EST 2020

% Result     : Theorem 6.84s
% Output     : Refutation 6.84s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 238 expanded)
%              Number of leaves         :   21 (  61 expanded)
%              Depth                    :   18
%              Number of atoms          :  343 (1151 expanded)
%              Number of equality atoms :  111 ( 343 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8659,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4547,f6073,f8629])).

fof(f8629,plain,(
    ~ spl220_2 ),
    inference(avatar_contradiction_clause,[],[f8628])).

fof(f8628,plain,
    ( $false
    | ~ spl220_2 ),
    inference(subsumption_resolution,[],[f6444,f8208])).

fof(f8208,plain,
    ( ! [X0,X1] : r1_xboole_0(X0,X1)
    | ~ spl220_2 ),
    inference(subsumption_resolution,[],[f6716,f3629])).

fof(f3629,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f131])).

fof(f131,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f6716,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,k1_xboole_0)
        | r1_xboole_0(X0,X1) )
    | ~ spl220_2 ),
    inference(backward_demodulation,[],[f3588,f6668])).

fof(f6668,plain,
    ( ! [X10] : k1_xboole_0 = X10
    | ~ spl220_2 ),
    inference(subsumption_resolution,[],[f6667,f3861])).

fof(f3861,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f2781])).

fof(f2781,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2294])).

fof(f2294,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f2293])).

fof(f2293,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f6667,plain,
    ( ! [X10] :
        ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,X10),k2_zfmisc_1(k1_xboole_0,X10))
        | k1_xboole_0 = X10 )
    | ~ spl220_2 ),
    inference(forward_demodulation,[],[f6666,f4652])).

fof(f4652,plain,(
    k1_xboole_0 = k10_relat_1(sK47,k1_xboole_0) ),
    inference(resolution,[],[f4294,f3039])).

fof(f3039,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1751])).

fof(f1751,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f773])).

fof(f773,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

fof(f4294,plain,(
    v1_relat_1(sK47) ),
    inference(resolution,[],[f2737,f2818])).

fof(f2818,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1607])).

fof(f1607,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f2737,plain,(
    m1_subset_1(sK47,k1_zfmisc_1(k2_zfmisc_1(sK44,sK45))) ),
    inference(cnf_transformation,[],[f2270])).

fof(f2270,plain,
    ( ~ r1_tarski(sK46,k8_relset_1(sK44,sK45,sK47,k7_relset_1(sK44,sK45,sK47,sK46)))
    & ( k1_xboole_0 = sK44
      | k1_xboole_0 != sK45 )
    & r1_tarski(sK46,sK44)
    & m1_subset_1(sK47,k1_zfmisc_1(k2_zfmisc_1(sK44,sK45)))
    & v1_funct_2(sK47,sK44,sK45)
    & v1_funct_1(sK47) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK44,sK45,sK46,sK47])],[f1549,f2269])).

fof(f2269,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(sK46,k8_relset_1(sK44,sK45,sK47,k7_relset_1(sK44,sK45,sK47,sK46)))
      & ( k1_xboole_0 = sK44
        | k1_xboole_0 != sK45 )
      & r1_tarski(sK46,sK44)
      & m1_subset_1(sK47,k1_zfmisc_1(k2_zfmisc_1(sK44,sK45)))
      & v1_funct_2(sK47,sK44,sK45)
      & v1_funct_1(sK47) ) ),
    introduced(choice_axiom,[])).

fof(f1549,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f1548])).

fof(f1548,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f1532])).

fof(f1532,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f1531])).

fof(f1531,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_2)).

fof(f6666,plain,
    ( ! [X10] :
        ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,X10),k2_zfmisc_1(k10_relat_1(sK47,k1_xboole_0),X10))
        | k1_xboole_0 = X10 )
    | ~ spl220_2 ),
    inference(forward_demodulation,[],[f6584,f4709])).

fof(f4709,plain,(
    k1_xboole_0 = k9_relat_1(sK47,k1_xboole_0) ),
    inference(resolution,[],[f4294,f3266])).

fof(f3266,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1869])).

fof(f1869,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f751])).

fof(f751,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).

fof(f6584,plain,
    ( ! [X10] :
        ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,X10),k2_zfmisc_1(k10_relat_1(sK47,k9_relat_1(sK47,k1_xboole_0)),X10))
        | k1_xboole_0 = X10 )
    | ~ spl220_2 ),
    inference(backward_demodulation,[],[f5136,f6571])).

fof(f6571,plain,
    ( k1_xboole_0 = sK46
    | ~ spl220_2 ),
    inference(subsumption_resolution,[],[f6570,f2775])).

fof(f2775,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f6570,plain,
    ( ~ r1_tarski(k1_xboole_0,sK46)
    | k1_xboole_0 = sK46
    | ~ spl220_2 ),
    inference(forward_demodulation,[],[f6091,f4546])).

fof(f4546,plain,
    ( k1_xboole_0 = sK44
    | ~ spl220_2 ),
    inference(avatar_component_clause,[],[f4545])).

fof(f4545,plain,
    ( spl220_2
  <=> k1_xboole_0 = sK44 ),
    introduced(avatar_definition,[new_symbols(naming,[spl220_2])])).

fof(f6091,plain,
    ( k1_xboole_0 = sK46
    | ~ r1_tarski(sK44,sK46)
    | ~ spl220_2 ),
    inference(backward_demodulation,[],[f4128,f4546])).

fof(f4128,plain,
    ( sK44 = sK46
    | ~ r1_tarski(sK44,sK46) ),
    inference(resolution,[],[f2738,f2783])).

fof(f2783,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2294])).

fof(f2738,plain,(
    r1_tarski(sK46,sK44) ),
    inference(cnf_transformation,[],[f2270])).

fof(f5136,plain,(
    ! [X10] :
      ( ~ r1_tarski(k2_zfmisc_1(sK46,X10),k2_zfmisc_1(k10_relat_1(sK47,k9_relat_1(sK47,sK46)),X10))
      | k1_xboole_0 = X10 ) ),
    inference(resolution,[],[f4415,f2816])).

fof(f2816,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1606])).

fof(f1606,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f333])).

fof(f333,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f4415,plain,(
    ~ r1_tarski(sK46,k10_relat_1(sK47,k9_relat_1(sK47,sK46))) ),
    inference(backward_demodulation,[],[f4406,f4281])).

fof(f4281,plain,(
    ! [X19] : k7_relset_1(sK44,sK45,sK47,X19) = k9_relat_1(sK47,X19) ),
    inference(resolution,[],[f2737,f2758])).

fof(f2758,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1565])).

fof(f1565,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1233])).

fof(f1233,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f4406,plain,(
    ~ r1_tarski(sK46,k10_relat_1(sK47,k7_relset_1(sK44,sK45,sK47,sK46))) ),
    inference(backward_demodulation,[],[f2740,f4272])).

fof(f4272,plain,(
    ! [X7] : k8_relset_1(sK44,sK45,sK47,X7) = k10_relat_1(sK47,X7) ),
    inference(resolution,[],[f2737,f2745])).

fof(f2745,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1554])).

fof(f1554,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1234])).

fof(f1234,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f2740,plain,(
    ~ r1_tarski(sK46,k8_relset_1(sK44,sK45,sK47,k7_relset_1(sK44,sK45,sK47,sK46))) ),
    inference(cnf_transformation,[],[f2270])).

fof(f3588,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2107])).

fof(f2107,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f138])).

fof(f138,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f6444,plain,
    ( ! [X233] : ~ r1_xboole_0(k2_tarski(sK46,X233),k1_zfmisc_1(k1_xboole_0))
    | ~ spl220_2 ),
    inference(backward_demodulation,[],[f5531,f4546])).

fof(f5531,plain,(
    ! [X233] : ~ r1_xboole_0(k2_tarski(sK46,X233),k1_zfmisc_1(sK44)) ),
    inference(resolution,[],[f4206,f3637])).

fof(f3637,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f2143])).

fof(f2143,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f413])).

fof(f413,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f4206,plain,(
    r2_hidden(sK46,k1_zfmisc_1(sK44)) ),
    inference(resolution,[],[f2738,f3862])).

fof(f3862,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f2790])).

fof(f2790,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2301])).

fof(f2301,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK55(X0,X1),X0)
            | ~ r2_hidden(sK55(X0,X1),X1) )
          & ( r1_tarski(sK55(X0,X1),X0)
            | r2_hidden(sK55(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK55])],[f2299,f2300])).

fof(f2300,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK55(X0,X1),X0)
          | ~ r2_hidden(sK55(X0,X1),X1) )
        & ( r1_tarski(sK55(X0,X1),X0)
          | r2_hidden(sK55(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2299,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f2298])).

fof(f2298,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f285])).

fof(f285,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f6073,plain,(
    spl220_1 ),
    inference(avatar_contradiction_clause,[],[f6072])).

fof(f6072,plain,
    ( $false
    | spl220_1 ),
    inference(subsumption_resolution,[],[f5954,f2738])).

fof(f5954,plain,
    ( ~ r1_tarski(sK46,sK44)
    | spl220_1 ),
    inference(backward_demodulation,[],[f5158,f5773])).

fof(f5773,plain,
    ( sK44 = k1_relat_1(sK47)
    | spl220_1 ),
    inference(backward_demodulation,[],[f4329,f5772])).

fof(f5772,plain,
    ( sK44 = k1_relset_1(sK44,sK45,sK47)
    | spl220_1 ),
    inference(subsumption_resolution,[],[f5771,f4543])).

fof(f4543,plain,
    ( k1_xboole_0 != sK45
    | spl220_1 ),
    inference(avatar_component_clause,[],[f4542])).

fof(f4542,plain,
    ( spl220_1
  <=> k1_xboole_0 = sK45 ),
    introduced(avatar_definition,[new_symbols(naming,[spl220_1])])).

fof(f5771,plain,
    ( sK44 = k1_relset_1(sK44,sK45,sK47)
    | k1_xboole_0 = sK45 ),
    inference(subsumption_resolution,[],[f5769,f2736])).

fof(f2736,plain,(
    v1_funct_2(sK47,sK44,sK45) ),
    inference(cnf_transformation,[],[f2270])).

fof(f5769,plain,
    ( sK44 = k1_relset_1(sK44,sK45,sK47)
    | ~ v1_funct_2(sK47,sK44,sK45)
    | k1_xboole_0 = sK45 ),
    inference(resolution,[],[f4327,f3277])).

fof(f3277,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | ~ sP25(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2595])).

fof(f2595,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP25(X0,X1,X2) ) ),
    inference(rectify,[],[f2594])).

fof(f2594,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP25(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f2236])).

fof(f2236,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP25(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP25])])).

fof(f4327,plain,(
    sP25(sK44,sK47,sK45) ),
    inference(resolution,[],[f2737,f3281])).

fof(f3281,plain,(
    ! [X2,X0,X1] :
      ( sP25(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2596])).

fof(f2596,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP25(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f2237])).

fof(f2237,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP25(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f1878,f2236])).

fof(f1878,plain,(
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
    inference(flattening,[],[f1877])).

fof(f1877,plain,(
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
    inference(ennf_transformation,[],[f1472])).

fof(f1472,axiom,(
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

fof(f4329,plain,(
    k1_relat_1(sK47) = k1_relset_1(sK44,sK45,sK47) ),
    inference(resolution,[],[f2737,f3285])).

fof(f3285,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1880])).

fof(f1880,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1227])).

fof(f1227,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f5158,plain,(
    ~ r1_tarski(sK46,k1_relat_1(sK47)) ),
    inference(subsumption_resolution,[],[f5123,f4294])).

fof(f5123,plain,
    ( ~ r1_tarski(sK46,k1_relat_1(sK47))
    | ~ v1_relat_1(sK47) ),
    inference(resolution,[],[f4415,f3007])).

fof(f3007,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1732])).

fof(f1732,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1731])).

fof(f1731,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f965])).

fof(f965,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f4547,plain,
    ( ~ spl220_1
    | spl220_2 ),
    inference(avatar_split_clause,[],[f2739,f4545,f4542])).

fof(f2739,plain,
    ( k1_xboole_0 = sK44
    | k1_xboole_0 != sK45 ),
    inference(cnf_transformation,[],[f2270])).
%------------------------------------------------------------------------------
