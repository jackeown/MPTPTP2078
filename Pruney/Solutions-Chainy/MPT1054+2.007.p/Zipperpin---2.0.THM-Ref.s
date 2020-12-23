%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lcQBpfa3Ru

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 172 expanded)
%              Number of leaves         :   42 (  76 expanded)
%              Depth                    :   13
%              Number of atoms          :  657 (1030 expanded)
%              Number of equality atoms :   64 ( 111 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(t171_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t171_funct_2])).

thf('0',plain,(
    ( k8_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('1',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('4',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( ( k8_relset_1 @ X36 @ X37 @ X35 @ X38 )
        = ( k10_relat_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('6',plain,(
    ! [X34: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X34 ) )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf('7',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('8',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('9',plain,(
    ! [X34: $i] :
      ( ( k2_funct_1 @ ( k6_partfun1 @ X34 ) )
      = ( k6_partfun1 @ X34 ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('10',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k10_relat_1 @ X30 @ X31 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X30 ) @ X31 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(fc24_relat_1,axiom,(
    ! [A: $i] :
      ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('13',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('14',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X23 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X27: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('16',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('17',plain,(
    ! [X27: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X27 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('18',plain,(
    ! [X29: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('19',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('20',plain,(
    ! [X29: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X29 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['11','14','17','20'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('22',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k7_relat_1 @ X22 @ X21 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X21 ) @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('23',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('24',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k7_relat_1 @ X22 @ X21 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X21 ) @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ ( k6_relat_1 @ X32 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('26',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('27',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('29',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X33 ) @ ( k6_partfun1 @ X32 ) )
      = ( k6_partfun1 @ ( k3_xboole_0 @ X32 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 )
        = ( k6_partfun1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X23 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 )
      = ( k6_partfun1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k6_partfun1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('35',plain,(
    ! [X20: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('36',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('37',plain,(
    ! [X20: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X20 ) )
      = X20 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X23 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k9_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['34','37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['21','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','40'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('43',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X24: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X24 ) @ X24 ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('48',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('49',plain,(
    ! [X24: $i] :
      ( v4_relat_1 @ ( k6_partfun1 @ X24 ) @ X24 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('51',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('52',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['50','51'])).

thf(t217_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v4_relat_1 @ C @ A ) )
         => ( v4_relat_1 @ C @ B ) ) ) )).

thf('53',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v4_relat_1 @ X16 @ X17 )
      | ( v4_relat_1 @ X16 @ X18 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t217_relat_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ sk_A )
      | ~ ( v4_relat_1 @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    | ( v4_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X23 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('57',plain,(
    v4_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['55','56'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('58',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14
        = ( k7_relat_1 @ X14 @ X15 ) )
      | ~ ( v4_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    | ( ( k6_partfun1 @ sk_B )
      = ( k7_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X23 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('61',plain,
    ( ( k6_partfun1 @ sk_B )
    = ( k7_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 )
      = ( k6_partfun1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('63',plain,
    ( ( k6_partfun1 @ sk_B )
    = ( k6_partfun1 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('65',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('66',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('69',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    sk_B != sk_B ),
    inference(demod,[status(thm)],['0','41','46','69'])).

thf('71',plain,(
    $false ),
    inference(simplify,[status(thm)],['70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lcQBpfa3Ru
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:23:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 127 iterations in 0.045s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.50  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.50  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.50  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.50  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.20/0.50  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.50  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.20/0.50  thf(t171_funct_2, conjecture,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.50       ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i]:
% 0.20/0.50        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.50          ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t171_funct_2])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (((k8_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ sk_B) != (sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t29_relset_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( m1_subset_1 @
% 0.20/0.50       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X39 : $i]:
% 0.20/0.50         (m1_subset_1 @ (k6_relat_1 @ X39) @ 
% 0.20/0.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.20/0.50  thf(redefinition_k6_partfun1, axiom,
% 0.20/0.50    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.20/0.50  thf('2', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X39 : $i]:
% 0.20/0.50         (m1_subset_1 @ (k6_partfun1 @ X39) @ 
% 0.20/0.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))),
% 0.20/0.50      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf(redefinition_k8_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.20/0.50          | ((k8_relset_1 @ X36 @ X37 @ X35 @ X38) = (k10_relat_1 @ X35 @ X38)))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 0.20/0.50           = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.50  thf(t67_funct_1, axiom,
% 0.20/0.50    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X34 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X34)) = (k6_relat_1 @ X34))),
% 0.20/0.50      inference('cnf', [status(esa)], [t67_funct_1])).
% 0.20/0.50  thf('7', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.50  thf('8', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X34 : $i]: ((k2_funct_1 @ (k6_partfun1 @ X34)) = (k6_partfun1 @ X34))),
% 0.20/0.50      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.20/0.50  thf(t155_funct_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.50       ( ( v2_funct_1 @ B ) =>
% 0.20/0.50         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X30 : $i, X31 : $i]:
% 0.20/0.50         (~ (v2_funct_1 @ X30)
% 0.20/0.50          | ((k10_relat_1 @ X30 @ X31)
% 0.20/0.50              = (k9_relat_1 @ (k2_funct_1 @ X30) @ X31))
% 0.20/0.50          | ~ (v1_funct_1 @ X30)
% 0.20/0.50          | ~ (v1_relat_1 @ X30))),
% 0.20/0.50      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((k10_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 0.20/0.50            = (k9_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 0.20/0.50          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.20/0.50          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.20/0.50          | ~ (v2_funct_1 @ (k6_partfun1 @ X0)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf(fc24_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.20/0.50       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.20/0.50       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.50  thf('12', plain, (![X23 : $i]: (v1_relat_1 @ (k6_relat_1 @ X23))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.20/0.50  thf('13', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.50  thf('14', plain, (![X23 : $i]: (v1_relat_1 @ (k6_partfun1 @ X23))),
% 0.20/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf(fc3_funct_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.50       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.50  thf('15', plain, (![X27 : $i]: (v1_funct_1 @ (k6_relat_1 @ X27))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.50  thf('16', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.50  thf('17', plain, (![X27 : $i]: (v1_funct_1 @ (k6_partfun1 @ X27))),
% 0.20/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf(fc4_funct_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.50       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.50  thf('18', plain, (![X29 : $i]: (v2_funct_1 @ (k6_relat_1 @ X29))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.20/0.50  thf('19', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.50  thf('20', plain, (![X29 : $i]: (v2_funct_1 @ (k6_partfun1 @ X29))),
% 0.20/0.50      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((k10_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 0.20/0.50           = (k9_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.20/0.50      inference('demod', [status(thm)], ['11', '14', '17', '20'])).
% 0.20/0.50  thf(t94_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X21 : $i, X22 : $i]:
% 0.20/0.50         (((k7_relat_1 @ X22 @ X21) = (k5_relat_1 @ (k6_relat_1 @ X21) @ X22))
% 0.20/0.50          | ~ (v1_relat_1 @ X22))),
% 0.20/0.50      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.20/0.50  thf('23', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X21 : $i, X22 : $i]:
% 0.20/0.50         (((k7_relat_1 @ X22 @ X21) = (k5_relat_1 @ (k6_partfun1 @ X21) @ X22))
% 0.20/0.50          | ~ (v1_relat_1 @ X22))),
% 0.20/0.50      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.50  thf(t43_funct_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.20/0.50       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (![X32 : $i, X33 : $i]:
% 0.20/0.50         ((k5_relat_1 @ (k6_relat_1 @ X33) @ (k6_relat_1 @ X32))
% 0.20/0.50           = (k6_relat_1 @ (k3_xboole_0 @ X32 @ X33)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.20/0.50  thf('26', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.50  thf('27', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.50  thf('28', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (![X32 : $i, X33 : $i]:
% 0.20/0.50         ((k5_relat_1 @ (k6_partfun1 @ X33) @ (k6_partfun1 @ X32))
% 0.20/0.50           = (k6_partfun1 @ (k3_xboole_0 @ X32 @ X33)))),
% 0.20/0.50      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((k7_relat_1 @ (k6_partfun1 @ X1) @ X0)
% 0.20/0.50            = (k6_partfun1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.20/0.50          | ~ (v1_relat_1 @ (k6_partfun1 @ X1)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['24', '29'])).
% 0.20/0.50  thf('31', plain, (![X23 : $i]: (v1_relat_1 @ (k6_partfun1 @ X23))),
% 0.20/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((k7_relat_1 @ (k6_partfun1 @ X1) @ X0)
% 0.20/0.50           = (k6_partfun1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.50  thf(t148_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (![X12 : $i, X13 : $i]:
% 0.20/0.50         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 0.20/0.50          | ~ (v1_relat_1 @ X12))),
% 0.20/0.50      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((k2_relat_1 @ (k6_partfun1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.20/0.50            = (k9_relat_1 @ (k6_partfun1 @ X1) @ X0))
% 0.20/0.50          | ~ (v1_relat_1 @ (k6_partfun1 @ X1)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['32', '33'])).
% 0.20/0.50  thf(t71_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.20/0.50       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.50  thf('35', plain, (![X20 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 0.20/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.50  thf('36', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.50  thf('37', plain, (![X20 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X20)) = (X20))),
% 0.20/0.50      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('38', plain, (![X23 : $i]: (v1_relat_1 @ (k6_partfun1 @ X23))),
% 0.20/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((k3_xboole_0 @ X1 @ X0) = (k9_relat_1 @ (k6_partfun1 @ X1) @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['34', '37', '38'])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((k10_relat_1 @ (k6_partfun1 @ X0) @ X1) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.50      inference('demod', [status(thm)], ['21', '39'])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 0.20/0.50           = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.50      inference('demod', [status(thm)], ['5', '40'])).
% 0.20/0.50  thf(commutativity_k2_tarski, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.20/0.50  thf(t12_setfam_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i]:
% 0.20/0.50         ((k1_setfam_1 @ (k2_tarski @ X7 @ X8)) = (k3_xboole_0 @ X7 @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.50      inference('sup+', [status(thm)], ['42', '43'])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i]:
% 0.20/0.50         ((k1_setfam_1 @ (k2_tarski @ X7 @ X8)) = (k3_xboole_0 @ X7 @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.50      inference('sup+', [status(thm)], ['44', '45'])).
% 0.20/0.50  thf('47', plain, (![X24 : $i]: (v4_relat_1 @ (k6_relat_1 @ X24) @ X24)),
% 0.20/0.50      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.20/0.50  thf('48', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.50  thf('49', plain, (![X24 : $i]: (v4_relat_1 @ (k6_partfun1 @ X24) @ X24)),
% 0.20/0.50      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.50  thf('50', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t3_subset, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      (![X9 : $i, X10 : $i]:
% 0.20/0.50         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.50  thf('52', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.50      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.50  thf(t217_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_tarski @ A @ B ) =>
% 0.20/0.50       ( ![C:$i]:
% 0.20/0.50         ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ A ) ) =>
% 0.20/0.50           ( v4_relat_1 @ C @ B ) ) ) ))).
% 0.20/0.50  thf('53', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X16)
% 0.20/0.50          | ~ (v4_relat_1 @ X16 @ X17)
% 0.20/0.50          | (v4_relat_1 @ X16 @ X18)
% 0.20/0.50          | ~ (r1_tarski @ X17 @ X18))),
% 0.20/0.50      inference('cnf', [status(esa)], [t217_relat_1])).
% 0.20/0.50  thf('54', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v4_relat_1 @ X0 @ sk_A)
% 0.20/0.50          | ~ (v4_relat_1 @ X0 @ sk_B)
% 0.20/0.50          | ~ (v1_relat_1 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ (k6_partfun1 @ sk_B))
% 0.20/0.50        | (v4_relat_1 @ (k6_partfun1 @ sk_B) @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['49', '54'])).
% 0.20/0.50  thf('56', plain, (![X23 : $i]: (v1_relat_1 @ (k6_partfun1 @ X23))),
% 0.20/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('57', plain, ((v4_relat_1 @ (k6_partfun1 @ sk_B) @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['55', '56'])).
% 0.20/0.50  thf(t209_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.50       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.20/0.50  thf('58', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i]:
% 0.20/0.50         (((X14) = (k7_relat_1 @ X14 @ X15))
% 0.20/0.50          | ~ (v4_relat_1 @ X14 @ X15)
% 0.20/0.50          | ~ (v1_relat_1 @ X14))),
% 0.20/0.50      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.20/0.50  thf('59', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ (k6_partfun1 @ sk_B))
% 0.20/0.50        | ((k6_partfun1 @ sk_B) = (k7_relat_1 @ (k6_partfun1 @ sk_B) @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.50  thf('60', plain, (![X23 : $i]: (v1_relat_1 @ (k6_partfun1 @ X23))),
% 0.20/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('61', plain,
% 0.20/0.50      (((k6_partfun1 @ sk_B) = (k7_relat_1 @ (k6_partfun1 @ sk_B) @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['59', '60'])).
% 0.20/0.50  thf('62', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((k7_relat_1 @ (k6_partfun1 @ X1) @ X0)
% 0.20/0.50           = (k6_partfun1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.50  thf('63', plain,
% 0.20/0.50      (((k6_partfun1 @ sk_B) = (k6_partfun1 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['61', '62'])).
% 0.20/0.50  thf('64', plain, (![X19 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 0.20/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.50  thf('65', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.50  thf('66', plain, (![X19 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X19)) = (X19))),
% 0.20/0.50      inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.50  thf('67', plain,
% 0.20/0.50      (((k1_relat_1 @ (k6_partfun1 @ sk_B)) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.20/0.50      inference('sup+', [status(thm)], ['63', '66'])).
% 0.20/0.50  thf('68', plain, (![X19 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X19)) = (X19))),
% 0.20/0.50      inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.50  thf('69', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['67', '68'])).
% 0.20/0.50  thf('70', plain, (((sk_B) != (sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['0', '41', '46', '69'])).
% 0.20/0.50  thf('71', plain, ($false), inference('simplify', [status(thm)], ['70'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
