%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t120_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:14 EDT 2019

% Result     : Theorem 6.63s
% Output     : Refutation 6.63s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 610 expanded)
%              Number of leaves         :   13 ( 128 expanded)
%              Depth                    :   16
%              Number of atoms          :  279 (1841 expanded)
%              Number of equality atoms :   32 ( 124 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3846,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f177,f419,f449,f3845])).

fof(f3845,plain,(
    ~ spl10_18 ),
    inference(avatar_contradiction_clause,[],[f3834])).

fof(f3834,plain,
    ( $false
    | ~ spl10_18 ),
    inference(unit_resulting_resolution,[],[f1648,f3802,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t120_funct_1.p',t1_subset)).

fof(f3802,plain,
    ( r2_hidden(sK3(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,sK1))
    | ~ spl10_18 ),
    inference(forward_demodulation,[],[f3787,f719])).

fof(f719,plain,(
    k1_funct_1(sK2,sK5(k8_relat_1(sK0,sK2),sK1,sK3(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1)))) = sK3(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f702,f216])).

fof(f216,plain,(
    k1_funct_1(k8_relat_1(sK0,sK2),sK5(k8_relat_1(sK0,sK2),sK1,sK3(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1)))) = sK3(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f93,f91,f130,f84])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK5(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK5(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t120_funct_1.p',d12_funct_1)).

fof(f130,plain,(
    r2_hidden(sK3(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1)),k9_relat_1(k8_relat_1(sK0,sK2),sK1)) ),
    inference(unit_resulting_resolution,[],[f47,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t120_funct_1.p',d3_tarski)).

fof(f47,plain,(
    ~ r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t120_funct_1.p',t120_funct_1)).

fof(f91,plain,(
    ! [X0] : v1_relat_1(k8_relat_1(X0,sK2)) ),
    inference(unit_resulting_resolution,[],[f45,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t120_funct_1.p',dt_k8_relat_1)).

fof(f45,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f93,plain,(
    ! [X0] : v1_funct_1(k8_relat_1(X0,sK2)) ),
    inference(unit_resulting_resolution,[],[f45,f46,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | v1_funct_1(k8_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t120_funct_1.p',fc9_funct_1)).

fof(f46,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f702,plain,(
    k1_funct_1(sK2,sK5(k8_relat_1(sK0,sK2),sK1,sK3(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1)))) = k1_funct_1(k8_relat_1(sK0,sK2),sK5(k8_relat_1(sK0,sK2),sK1,sK3(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1)))) ),
    inference(unit_resulting_resolution,[],[f46,f45,f91,f93,f214,f87])).

fof(f87,plain,(
    ! [X2,X0,X3] :
      ( ~ v1_funct_1(k8_relat_1(X0,X2))
      | ~ v1_relat_1(k8_relat_1(X0,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X3,k1_relat_1(k8_relat_1(X0,X2)))
      | k1_funct_1(X2,X3) = k1_funct_1(k8_relat_1(X0,X2),X3) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X3,k1_relat_1(X1))
      | k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
      | k8_relat_1(X0,X2) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) ) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) )
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X3),X0)
                    & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t120_funct_1.p',t85_funct_1)).

fof(f214,plain,(
    r2_hidden(sK5(k8_relat_1(sK0,sK2),sK1,sK3(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1))),k1_relat_1(k8_relat_1(sK0,sK2))) ),
    inference(unit_resulting_resolution,[],[f93,f91,f130,f86])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK5(X0,X1,X3),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK5(X0,X1,X3),k1_relat_1(X0))
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3787,plain,
    ( r2_hidden(k1_funct_1(sK2,sK5(k8_relat_1(sK0,sK2),sK1,sK3(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK1))
    | ~ spl10_18 ),
    inference(unit_resulting_resolution,[],[f45,f46,f215,f705,f83])).

fof(f83,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X1)
      | r2_hidden(k1_funct_1(X0,X4),X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X1)
      | k1_funct_1(X0,X4) != X3
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f705,plain,
    ( r2_hidden(sK5(k8_relat_1(sK0,sK2),sK1,sK3(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ spl10_18 ),
    inference(unit_resulting_resolution,[],[f494,f214,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f494,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k8_relat_1(X0,sK2)),k1_relat_1(sK2))
    | ~ spl10_18 ),
    inference(duplicate_literal_removal,[],[f493])).

fof(f493,plain,
    ( ! [X0] :
        ( r1_tarski(k1_relat_1(k8_relat_1(X0,sK2)),k1_relat_1(sK2))
        | r1_tarski(k1_relat_1(k8_relat_1(X0,sK2)),k1_relat_1(sK2)) )
    | ~ spl10_18 ),
    inference(resolution,[],[f482,f51])).

fof(f482,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(sK3(X2,k1_relat_1(sK2)),k1_relat_1(k8_relat_1(X3,sK2)))
        | r1_tarski(X2,k1_relat_1(sK2)) )
    | ~ spl10_18 ),
    inference(resolution,[],[f474,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f474,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k1_relat_1(sK2))
        | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK2))) )
    | ~ spl10_18 ),
    inference(resolution,[],[f448,f91])).

fof(f448,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(k8_relat_1(X0,sK2))
        | r2_hidden(X1,k1_relat_1(sK2))
        | ~ r2_hidden(X1,k1_relat_1(k8_relat_1(X0,sK2))) )
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f447])).

fof(f447,plain,
    ( spl10_18
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(k8_relat_1(X0,sK2))
        | r2_hidden(X1,k1_relat_1(sK2))
        | ~ r2_hidden(X1,k1_relat_1(k8_relat_1(X0,sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f215,plain,(
    r2_hidden(sK5(k8_relat_1(sK0,sK2),sK1,sK3(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1))),sK1) ),
    inference(unit_resulting_resolution,[],[f93,f91,f130,f85])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1648,plain,(
    ~ m1_subset_1(sK3(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f131,f1641,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t120_funct_1.p',t2_subset)).

fof(f1641,plain,(
    ~ v1_xboole_0(k9_relat_1(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f1626,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t120_funct_1.p',t7_boole)).

fof(f1626,plain,(
    r2_hidden(sK9(k9_relat_1(k8_relat_1(sK0,sK2),sK1)),k9_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f1610,f274])).

fof(f274,plain,(
    k1_funct_1(sK2,sK5(k8_relat_1(sK0,sK2),sK1,sK9(k9_relat_1(k8_relat_1(sK0,sK2),sK1)))) = sK9(k9_relat_1(k8_relat_1(sK0,sK2),sK1)) ),
    inference(forward_demodulation,[],[f262,f226])).

fof(f226,plain,(
    k1_funct_1(k8_relat_1(sK0,sK2),sK5(k8_relat_1(sK0,sK2),sK1,sK9(k9_relat_1(k8_relat_1(sK0,sK2),sK1)))) = sK9(k9_relat_1(k8_relat_1(sK0,sK2),sK1)) ),
    inference(unit_resulting_resolution,[],[f93,f91,f223,f84])).

fof(f223,plain,(
    r2_hidden(sK9(k9_relat_1(k8_relat_1(sK0,sK2),sK1)),k9_relat_1(k8_relat_1(sK0,sK2),sK1)) ),
    inference(unit_resulting_resolution,[],[f78,f219,f76])).

fof(f219,plain,(
    ~ v1_xboole_0(k9_relat_1(k8_relat_1(sK0,sK2),sK1)) ),
    inference(unit_resulting_resolution,[],[f130,f79])).

fof(f78,plain,(
    ! [X0] : m1_subset_1(sK9(X0),X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t120_funct_1.p',existence_m1_subset_1)).

fof(f262,plain,(
    k1_funct_1(sK2,sK5(k8_relat_1(sK0,sK2),sK1,sK9(k9_relat_1(k8_relat_1(sK0,sK2),sK1)))) = k1_funct_1(k8_relat_1(sK0,sK2),sK5(k8_relat_1(sK0,sK2),sK1,sK9(k9_relat_1(k8_relat_1(sK0,sK2),sK1)))) ),
    inference(unit_resulting_resolution,[],[f46,f45,f91,f93,f224,f87])).

fof(f224,plain,(
    r2_hidden(sK5(k8_relat_1(sK0,sK2),sK1,sK9(k9_relat_1(k8_relat_1(sK0,sK2),sK1))),k1_relat_1(k8_relat_1(sK0,sK2))) ),
    inference(unit_resulting_resolution,[],[f93,f91,f223,f86])).

fof(f1610,plain,(
    r2_hidden(k1_funct_1(sK2,sK5(k8_relat_1(sK0,sK2),sK1,sK9(k9_relat_1(k8_relat_1(sK0,sK2),sK1)))),k9_relat_1(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f45,f46,f225,f260,f83])).

fof(f260,plain,(
    r2_hidden(sK5(k8_relat_1(sK0,sK2),sK1,sK9(k9_relat_1(k8_relat_1(sK0,sK2),sK1))),k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f46,f45,f93,f91,f224,f90])).

fof(f90,plain,(
    ! [X4,X2,X0] :
      ( ~ v1_funct_1(k8_relat_1(X0,X2))
      | ~ v1_relat_1(k8_relat_1(X0,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(X4,k1_relat_1(X2))
      | ~ r2_hidden(X4,k1_relat_1(k8_relat_1(X0,X2))) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(X4,k1_relat_1(X2))
      | ~ r2_hidden(X4,k1_relat_1(X1))
      | k8_relat_1(X0,X2) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f225,plain,(
    r2_hidden(sK5(k8_relat_1(sK0,sK2),sK1,sK9(k9_relat_1(k8_relat_1(sK0,sK2),sK1))),sK1) ),
    inference(unit_resulting_resolution,[],[f93,f91,f223,f85])).

fof(f131,plain,(
    ~ r2_hidden(sK3(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f47,f52])).

fof(f449,plain,
    ( ~ spl10_15
    | ~ spl10_3
    | spl10_18 ),
    inference(avatar_split_clause,[],[f104,f447,f171,f410])).

fof(f410,plain,
    ( spl10_15
  <=> ~ v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f171,plain,
    ( spl10_3
  <=> ~ v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k8_relat_1(X0,sK2))
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | r2_hidden(X1,k1_relat_1(sK2))
      | ~ r2_hidden(X1,k1_relat_1(k8_relat_1(X0,sK2))) ) ),
    inference(resolution,[],[f93,f90])).

fof(f419,plain,(
    spl10_15 ),
    inference(avatar_contradiction_clause,[],[f416])).

fof(f416,plain,
    ( $false
    | ~ spl10_15 ),
    inference(unit_resulting_resolution,[],[f46,f411])).

fof(f411,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f410])).

fof(f177,plain,(
    spl10_3 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f45,f172])).

fof(f172,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f171])).
%------------------------------------------------------------------------------
