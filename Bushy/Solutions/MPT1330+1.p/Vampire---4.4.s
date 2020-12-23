%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_2__t52_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:40 EDT 2019

% Result     : Theorem 0.69s
% Output     : Refutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 635 expanded)
%              Number of leaves         :   19 ( 208 expanded)
%              Depth                    :   22
%              Number of atoms          :  354 (3679 expanded)
%              Number of equality atoms :  129 (1601 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f617,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f134,f367,f616])).

fof(f616,plain,
    ( ~ spl6_0
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f615])).

fof(f615,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f612,f577])).

fof(f577,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,k1_xboole_0)
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f412,f384])).

fof(f384,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f133,f135])).

fof(f135,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f75,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t52_tops_2.p',d3_struct_0)).

fof(f75,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    & ( k2_struct_0(sK0) = k1_xboole_0
      | k2_struct_0(sK1) != k1_xboole_0 )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f65,f64,f63])).

fof(f63,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
                & ( k2_struct_0(X0) = k1_xboole_0
                  | k2_struct_0(X1) != k1_xboole_0 )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k2_struct_0(sK0) = k1_xboole_0
                | k2_struct_0(X1) != k1_xboole_0 )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k2_struct_0(X0) = k1_xboole_0
                | k2_struct_0(X1) != k1_xboole_0 )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) )
          & l1_struct_0(X1) )
     => ( ? [X2] :
            ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,k2_struct_0(sK1))
            & ( k2_struct_0(X0) = k1_xboole_0
              | k2_struct_0(sK1) != k1_xboole_0 )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) )
        & l1_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
          & ( k2_struct_0(X0) = k1_xboole_0
            | k2_struct_0(X1) != k1_xboole_0 )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) )
     => ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,k2_struct_0(X1))
        & ( k2_struct_0(X0) = k1_xboole_0
          | k2_struct_0(X1) != k1_xboole_0 )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k2_struct_0(X0) = k1_xboole_0
                | k2_struct_0(X1) != k1_xboole_0 )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k2_struct_0(X0) = k1_xboole_0
                | k2_struct_0(X1) != k1_xboole_0 )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,plain,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) )
               => ( ( k2_struct_0(X1) = k1_xboole_0
                   => k2_struct_0(X0) = k1_xboole_0 )
                 => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( k2_struct_0(X1) = k1_xboole_0
                   => k2_struct_0(X0) = k1_xboole_0 )
                 => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k2_struct_0(X1) = k1_xboole_0
                 => k2_struct_0(X0) = k1_xboole_0 )
               => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t52_tops_2.p',t52_tops_2)).

fof(f133,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl6_2
  <=> k2_struct_0(sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f412,plain,
    ( u1_struct_0(sK0) != k10_relat_1(sK2,k1_xboole_0)
    | ~ spl6_0 ),
    inference(backward_demodulation,[],[f381,f337])).

fof(f337,plain,(
    u1_struct_0(sK0) != k10_relat_1(sK2,u1_struct_0(sK1)) ),
    inference(superposition,[],[f241,f172])).

fof(f172,plain,(
    ! [X0] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(resolution,[],[f78,f111])).

fof(f111,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t52_tops_2.p',redefinition_k8_relset_1)).

fof(f78,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f66])).

fof(f241,plain,(
    u1_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f240,f135])).

fof(f240,plain,(
    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f80,f136])).

fof(f136,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f76,f83])).

fof(f76,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f80,plain,(
    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f66])).

fof(f381,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | ~ spl6_0 ),
    inference(backward_demodulation,[],[f124,f136])).

fof(f124,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl6_0
  <=> k2_struct_0(sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f612,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(resolution,[],[f610,f408])).

fof(f408,plain,
    ( r1_tarski(k2_relat_1(sK2),k1_xboole_0)
    | ~ spl6_0 ),
    inference(backward_demodulation,[],[f381,f276])).

fof(f276,plain,(
    r1_tarski(k2_relat_1(sK2),u1_struct_0(sK1)) ),
    inference(resolution,[],[f274,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t52_tops_2.p',t3_subset)).

fof(f274,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f273,f78])).

fof(f273,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(superposition,[],[f100,f174])).

fof(f174,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f78,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t52_tops_2.p',redefinition_k2_relset_1)).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t52_tops_2.p',dt_k2_relset_1)).

fof(f610,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_relat_1(sK2),X1)
        | k1_xboole_0 = k10_relat_1(sK2,X1) )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f608,f424])).

fof(f424,plain,
    ( ! [X2] : r1_tarski(k10_relat_1(sK2,X2),k1_xboole_0)
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f384,f341])).

fof(f341,plain,(
    ! [X2] : r1_tarski(k10_relat_1(sK2,X2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f339,f92])).

fof(f339,plain,(
    ! [X0] : m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f338,f78])).

fof(f338,plain,(
    ! [X0] :
      ( m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ) ),
    inference(superposition,[],[f110,f172])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t52_tops_2.p',dt_k8_relset_1)).

fof(f608,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_relat_1(sK2),X1)
        | k1_xboole_0 = k10_relat_1(sK2,X1)
        | ~ r1_tarski(k10_relat_1(sK2,X1),k1_xboole_0) )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(resolution,[],[f601,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t52_tops_2.p',d10_xboole_0)).

fof(f601,plain,
    ( ! [X1] :
        ( r1_tarski(k1_xboole_0,k10_relat_1(sK2,X1))
        | ~ r1_tarski(k2_relat_1(sK2),X1) )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f600,f176])).

fof(f176,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f78,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t52_tops_2.p',cc1_relset_1)).

fof(f600,plain,
    ( ! [X1] :
        ( r1_tarski(k1_xboole_0,k10_relat_1(sK2,X1))
        | ~ r1_tarski(k2_relat_1(sK2),X1)
        | ~ v1_relat_1(sK2) )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(superposition,[],[f96,f594])).

fof(f594,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f209,f554])).

fof(f554,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f461,f467])).

fof(f467,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f456,f427])).

fof(f427,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f384,f387])).

fof(f387,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl6_0 ),
    inference(backward_demodulation,[],[f381,f77])).

fof(f77,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f66])).

fof(f456,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(resolution,[],[f436,f119])).

fof(f119,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
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
    inference(nnf_transformation,[],[f57])).

fof(f57,plain,(
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
    inference(flattening,[],[f56])).

fof(f56,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/tops_2__t52_tops_2.p',d1_funct_2)).

fof(f436,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f388,f384])).

fof(f388,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ spl6_0 ),
    inference(backward_demodulation,[],[f381,f78])).

fof(f461,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_relat_1(sK2)
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(resolution,[],[f436,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t52_tops_2.p',redefinition_k1_relset_1)).

fof(f209,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(resolution,[],[f176,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t52_tops_2.p',t169_relat_1)).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t52_tops_2.p',t178_relat_1)).

fof(f367,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f366])).

fof(f366,plain,
    ( $false
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f363,f337])).

fof(f363,plain,
    ( u1_struct_0(sK0) = k10_relat_1(sK2,u1_struct_0(sK1))
    | ~ spl6_1 ),
    inference(resolution,[],[f362,f276])).

fof(f362,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_relat_1(sK2),X1)
        | u1_struct_0(sK0) = k10_relat_1(sK2,X1) )
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f360,f341])).

fof(f360,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_relat_1(sK2),X1)
        | u1_struct_0(sK0) = k10_relat_1(sK2,X1)
        | ~ r1_tarski(k10_relat_1(sK2,X1),u1_struct_0(sK0)) )
    | ~ spl6_1 ),
    inference(resolution,[],[f336,f91])).

fof(f336,plain,
    ( ! [X1] :
        ( r1_tarski(u1_struct_0(sK0),k10_relat_1(sK2,X1))
        | ~ r1_tarski(k2_relat_1(sK2),X1) )
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f334,f176])).

fof(f334,plain,
    ( ! [X1] :
        ( r1_tarski(u1_struct_0(sK0),k10_relat_1(sK2,X1))
        | ~ r1_tarski(k2_relat_1(sK2),X1)
        | ~ v1_relat_1(sK2) )
    | ~ spl6_1 ),
    inference(superposition,[],[f96,f325])).

fof(f325,plain,
    ( u1_struct_0(sK0) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f318,f209])).

fof(f318,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f182,f175])).

fof(f175,plain,(
    k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f78,f98])).

fof(f182,plain,
    ( u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f181,f139])).

fof(f139,plain,
    ( u1_struct_0(sK1) != k1_xboole_0
    | ~ spl6_1 ),
    inference(superposition,[],[f127,f136])).

fof(f127,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl6_1
  <=> k2_struct_0(sK1) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f181,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f173,f77])).

fof(f173,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(resolution,[],[f78,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f72])).

fof(f134,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f79,f132,f126])).

fof(f79,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | k2_struct_0(sK1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).
%------------------------------------------------------------------------------
