%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : setfam_1__t59_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:19 EDT 2019

% Result     : Theorem 7.68s
% Output     : Refutation 7.68s
% Verified   : 
% Statistics : Number of formulae       :   34 ( 142 expanded)
%              Number of leaves         :    5 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   85 ( 417 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11352,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f34,f246,f83,f2952,f2940,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X3,X2)
      | r2_hidden(X1,X3)
      | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <=> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <=> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( r2_hidden(X1,X0)
       => ( r2_hidden(X1,k8_setfam_1(X0,X2))
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
             => r2_hidden(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t59_setfam_1.p',t58_setfam_1)).

fof(f2940,plain,(
    ~ r2_hidden(sK4(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)),sK3(sK4(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)),sK1)) ),
    inference(unit_resulting_resolution,[],[f37,f84,f246,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,sK3(X1,X2))
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | r2_hidden(X1,k8_setfam_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f84,plain,(
    ~ r2_hidden(sK4(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)),k8_setfam_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f36,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t59_setfam_1.p',d3_tarski)).

fof(f36,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t59_setfam_1.p',t59_setfam_1)).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f2952,plain,(
    r2_hidden(sK3(sK4(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)),sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f37,f84,f246,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ r2_hidden(X0,X1)
      | r2_hidden(sK3(X0,sK1),sK2)
      | r2_hidden(X0,k8_setfam_1(X1,sK1)) ) ),
    inference(resolution,[],[f55,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X1,X2),X2)
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | r2_hidden(X1,k8_setfam_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f55,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f35,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f35,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f83,plain,(
    r2_hidden(sK4(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)),k8_setfam_1(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f36,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f246,plain,(
    r2_hidden(sK4(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)),sK0) ),
    inference(unit_resulting_resolution,[],[f86,f83,f44])).

fof(f86,plain,(
    r1_tarski(k8_setfam_1(sK0,sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f57,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t59_setfam_1.p',t3_subset)).

fof(f57,plain,(
    m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f34,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t59_setfam_1.p',dt_k8_setfam_1)).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
