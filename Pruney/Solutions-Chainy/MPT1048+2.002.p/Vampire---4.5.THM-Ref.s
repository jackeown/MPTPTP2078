%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 368 expanded)
%              Number of leaves         :    6 (  73 expanded)
%              Depth                    :    9
%              Number of atoms          :  197 (1768 expanded)
%              Number of equality atoms :   17 ( 111 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f106,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f20,f16,f18,f17,f21,f80,f82,f96,f95,f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | ~ r1_partfun1(X2,X4)
      | ~ r1_relset_1(X0,X1,X3,X2)
      | r1_partfun1(X3,X4) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( r1_partfun1(X3,X4)
              | ~ r1_relset_1(X0,X1,X3,X2)
              | ~ r1_partfun1(X2,X4)
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( r1_partfun1(X3,X4)
              | ~ r1_relset_1(X0,X1,X3,X2)
              | ~ r1_partfun1(X2,X4)
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( v1_funct_1(X4)
                & v1_relat_1(X4) )
             => ( ( r1_relset_1(X0,X1,X3,X2)
                  & r1_partfun1(X2,X4) )
               => r1_partfun1(X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_partfun1)).

fof(f95,plain,(
    ~ r1_partfun1(sK3,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))) ),
    inference(unit_resulting_resolution,[],[f16,f17,f82,f79,f71,f81,f41])).

fof(f41,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X5,X0)
      | ~ r1_partfun1(X2,X5)
      | r2_hidden(X5,k5_partfun1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X5,X0)
      | ~ r1_partfun1(X2,X5)
      | r2_hidden(X5,X3)
      | k5_partfun1(X0,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X4 != X5
      | ~ v1_partfun1(X5,X0)
      | ~ r1_partfun1(X2,X5)
      | r2_hidden(X4,X3)
      | k5_partfun1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).

fof(f81,plain,(
    m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f74,f75])).

fof(f75,plain,(
    sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)) = sK6(sK0,sK1,sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))) ),
    inference(unit_resulting_resolution,[],[f20,f21,f70,f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK6(X0,X1,X2,X4) = X4
      | ~ r2_hidden(X4,k5_partfun1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK6(X0,X1,X2,X4) = X4
      | ~ r2_hidden(X4,X3)
      | k5_partfun1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f70,plain,(
    r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k5_partfun1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f19,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f19,plain,(
    ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          & r1_relset_1(X0,X1,X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          & r1_relset_1(X0,X1,X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X3) )
           => ( r1_relset_1(X0,X1,X3,X2)
             => r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( r1_relset_1(X0,X1,X3,X2)
           => r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t165_funct_2)).

fof(f74,plain,(
    m1_subset_1(sK6(sK0,sK1,sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f20,f21,f70,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X4,k5_partfun1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(sK6(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X4,X3)
      | k5_partfun1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f71,plain,(
    ~ r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k5_partfun1(sK0,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f19,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f79,plain,(
    v1_partfun1(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),sK0) ),
    inference(backward_demodulation,[],[f76,f75])).

fof(f76,plain,(
    v1_partfun1(sK6(sK0,sK1,sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))),sK0) ),
    inference(unit_resulting_resolution,[],[f20,f21,f70,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(sK6(X0,X1,X2,X4),X0)
      | ~ r2_hidden(X4,k5_partfun1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(sK6(X0,X1,X2,X4),X0)
      | ~ r2_hidden(X4,X3)
      | k5_partfun1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f96,plain,(
    v1_relat_1(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))) ),
    inference(unit_resulting_resolution,[],[f39,f81,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f39,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f82,plain,(
    v1_funct_1(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))) ),
    inference(forward_demodulation,[],[f73,f75])).

fof(f73,plain,(
    v1_funct_1(sK6(sK0,sK1,sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))) ),
    inference(unit_resulting_resolution,[],[f20,f21,f70,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(sK6(X0,X1,X2,X4))
      | ~ r2_hidden(X4,k5_partfun1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(sK6(X0,X1,X2,X4))
      | ~ r2_hidden(X4,X3)
      | k5_partfun1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f80,plain,(
    r1_partfun1(sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))) ),
    inference(backward_demodulation,[],[f77,f75])).

fof(f77,plain,(
    r1_partfun1(sK2,sK6(sK0,sK1,sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))) ),
    inference(unit_resulting_resolution,[],[f20,f21,f70,f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r1_partfun1(X2,sK6(X0,X1,X2,X4))
      | ~ r2_hidden(X4,k5_partfun1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r1_partfun1(X2,sK6(X0,X1,X2,X4))
      | ~ r2_hidden(X4,X3)
      | k5_partfun1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f21,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f9])).

fof(f17,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f9])).

fof(f18,plain,(
    r1_relset_1(sK0,sK1,sK3,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f16,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f20,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:21:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.48  % (2168)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (2177)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.50  % (2168)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f106,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f20,f16,f18,f17,f21,f80,f82,f96,f95,f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_relat_1(X4) | ~v1_funct_1(X4) | ~r1_partfun1(X2,X4) | ~r1_relset_1(X0,X1,X3,X2) | r1_partfun1(X3,X4)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (! [X3] : (! [X4] : (r1_partfun1(X3,X4) | ~r1_relset_1(X0,X1,X3,X2) | ~r1_partfun1(X2,X4) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.50    inference(flattening,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (! [X3] : (! [X4] : ((r1_partfun1(X3,X4) | (~r1_relset_1(X0,X1,X3,X2) | ~r1_partfun1(X2,X4))) | (~v1_funct_1(X4) | ~v1_relat_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ((v1_funct_1(X4) & v1_relat_1(X4)) => ((r1_relset_1(X0,X1,X3,X2) & r1_partfun1(X2,X4)) => r1_partfun1(X3,X4)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_partfun1)).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    ~r1_partfun1(sK3,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f16,f17,f82,f79,f71,f81,f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X2,X0,X5,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X5,X0) | ~r1_partfun1(X2,X5) | r2_hidden(X5,k5_partfun1(X0,X1,X2))) )),
% 0.20/0.50    inference(equality_resolution,[],[f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X2,X0,X5,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X5,X0) | ~r1_partfun1(X2,X5) | r2_hidden(X5,X3) | k5_partfun1(X0,X1,X2) != X3) )),
% 0.20/0.50    inference(equality_resolution,[],[f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X4 != X5 | ~v1_partfun1(X5,X0) | ~r1_partfun1(X2,X5) | r2_hidden(X4,X3) | k5_partfun1(X0,X1,X2) != X3) )),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.50    inference(flattening,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.50    inference(forward_demodulation,[],[f74,f75])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)) = sK6(sK0,sK1,sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f20,f21,f70,f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK6(X0,X1,X2,X4) = X4 | ~r2_hidden(X4,k5_partfun1(X0,X1,X2))) )),
% 0.20/0.50    inference(equality_resolution,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK6(X0,X1,X2,X4) = X4 | ~r2_hidden(X4,X3) | k5_partfun1(X0,X1,X2) != X3) )),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k5_partfun1(sK0,sK1,sK2))),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f19,f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ~r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) & r1_relset_1(X0,X1,X3,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.20/0.50    inference(flattening,[],[f8])).
% 0.20/0.50  fof(f8,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) & r1_relset_1(X0,X1,X3,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (r1_relset_1(X0,X1,X3,X2) => r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)))))),
% 0.20/0.50    inference(negated_conjecture,[],[f6])).
% 0.20/0.50  fof(f6,conjecture,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (r1_relset_1(X0,X1,X3,X2) => r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t165_funct_2)).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    m1_subset_1(sK6(sK0,sK1,sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f20,f21,f70,f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~r2_hidden(X4,k5_partfun1(X0,X1,X2))) )),
% 0.20/0.50    inference(equality_resolution,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(sK6(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X4,X3) | k5_partfun1(X0,X1,X2) != X3) )),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    ~r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k5_partfun1(sK0,sK1,sK3))),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f19,f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    v1_partfun1(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),sK0)),
% 0.20/0.50    inference(backward_demodulation,[],[f76,f75])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    v1_partfun1(sK6(sK0,sK1,sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))),sK0)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f20,f21,f70,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(sK6(X0,X1,X2,X4),X0) | ~r2_hidden(X4,k5_partfun1(X0,X1,X2))) )),
% 0.20/0.50    inference(equality_resolution,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(sK6(X0,X1,X2,X4),X0) | ~r2_hidden(X4,X3) | k5_partfun1(X0,X1,X2) != X3) )),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f96,plain,(
% 0.20/0.50    v1_relat_1(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f39,f81,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    v1_funct_1(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))),
% 0.20/0.50    inference(forward_demodulation,[],[f73,f75])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    v1_funct_1(sK6(sK0,sK1,sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))))),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f20,f21,f70,f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(sK6(X0,X1,X2,X4)) | ~r2_hidden(X4,k5_partfun1(X0,X1,X2))) )),
% 0.20/0.50    inference(equality_resolution,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(sK6(X0,X1,X2,X4)) | ~r2_hidden(X4,X3) | k5_partfun1(X0,X1,X2) != X3) )),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    r1_partfun1(sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))),
% 0.20/0.50    inference(backward_demodulation,[],[f77,f75])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    r1_partfun1(sK2,sK6(sK0,sK1,sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))))),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f20,f21,f70,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r1_partfun1(X2,sK6(X0,X1,X2,X4)) | ~r2_hidden(X4,k5_partfun1(X0,X1,X2))) )),
% 0.20/0.50    inference(equality_resolution,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r1_partfun1(X2,sK6(X0,X1,X2,X4)) | ~r2_hidden(X4,X3) | k5_partfun1(X0,X1,X2) != X3) )),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    r1_relset_1(sK0,sK1,sK3,sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    v1_funct_1(sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    v1_funct_1(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (2168)------------------------------
% 0.20/0.50  % (2168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (2168)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (2168)Memory used [KB]: 6396
% 0.20/0.50  % (2168)Time elapsed: 0.088 s
% 0.20/0.50  % (2168)------------------------------
% 0.20/0.50  % (2168)------------------------------
% 0.20/0.50  % (2163)Success in time 0.147 s
%------------------------------------------------------------------------------
