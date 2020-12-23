%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YN2M3MlwdH

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:38 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 512 expanded)
%              Number of leaves         :   43 ( 179 expanded)
%              Depth                    :   19
%              Number of atoms          : 1363 (5114 expanded)
%              Number of equality atoms :   95 ( 335 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ X30 @ ( k1_relat_1 @ X31 ) )
      | ( r1_tarski @ X30 @ ( k10_relat_1 @ X31 @ ( k9_relat_1 @ X31 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k10_relat_1 @ X16 @ X17 )
        = ( k10_relat_1 @ X16 @ ( k3_xboole_0 @ ( k2_relat_1 @ X16 ) @ X17 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X14 @ X15 ) @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('6',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ( v4_relat_1 @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( v4_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('9',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( v4_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf(t38_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( ( ( k7_relset_1 @ A @ B @ C @ A )
            = ( k2_relset_1 @ A @ B @ C ) )
          & ( ( k8_relset_1 @ A @ B @ C @ B )
            = ( k1_relset_1 @ A @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_relset_1])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( v4_relat_1 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('14',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v4_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('18',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v1_relat_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('19',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['16','19'])).

thf(t217_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v4_relat_1 @ C @ A ) )
         => ( v4_relat_1 @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v4_relat_1 @ X20 @ X21 )
      | ( v4_relat_1 @ X20 @ X22 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t217_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ sk_A )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) ) )
      | ( v4_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('25',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18
        = ( k7_relat_1 @ X18 @ X19 ) )
      | ~ ( v4_relat_1 @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) ) )
      | ( ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) ) @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X24: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('34',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ ( k6_relat_1 @ X32 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('36',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k7_relat_1 @ X26 @ X25 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X25 ) @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X24: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['34','41'])).

thf('43',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ X0 )
      = ( k3_xboole_0 @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33','44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['4','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ X0 )
      = ( k3_xboole_0 @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33','44','45'])).

thf('49',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X14 @ X15 ) @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('52',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ X0 ) )
      | ( ( k1_relat_1 @ sk_C )
        = ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('56',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ X0 ) )
      | ( ( k1_relat_1 @ sk_C )
        = ( k10_relat_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['3','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('60',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('62',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X54 ) @ X55 )
      | ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X56 ) ) )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X56 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( v4_relat_1 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('66',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18
        = ( k7_relat_1 @ X18 @ X19 ) )
      | ~ ( v4_relat_1 @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('70',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('72',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('74',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( v5_relat_1 @ X37 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('77',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['75','76'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('78',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v5_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('79',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('81',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( v4_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('83',plain,(
    v4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18
        = ( k7_relat_1 @ X18 @ X19 ) )
      | ~ ( v4_relat_1 @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('85',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ( ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('87',plain,
    ( ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) )
    = ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('89',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    = ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup+',[status(thm)],['87','90'])).

thf('92',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('93',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k10_relat_1 @ X16 @ X17 )
        = ( k10_relat_1 @ X16 @ ( k3_xboole_0 @ ( k2_relat_1 @ X16 ) @ X17 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('95',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('97',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['58','59','74','97'])).

thf('99',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['99'])).

thf('101',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('102',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k1_relset_1 @ X41 @ X42 @ X40 )
        = ( k1_relat_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('103',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['100','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('106',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( ( k7_relset_1 @ X47 @ X48 @ X46 @ X49 )
        = ( k9_relat_1 @ X46 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['99'])).

thf('109',plain,
    ( ( ( k9_relat_1 @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('111',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18
        = ( k7_relat_1 @ X18 @ X19 ) )
      | ~ ( v4_relat_1 @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('112',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('114',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('116',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('118',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('120',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( ( k2_relset_1 @ X44 @ X45 @ X43 )
        = ( k2_relat_1 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('121',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['109','118','121'])).

thf('123',plain,
    ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['99'])).

thf('125',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
 != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['123','124'])).

thf('126',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['104','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('128',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ( ( k8_relset_1 @ X51 @ X52 @ X50 @ X53 )
        = ( k10_relat_1 @ X50 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ( k10_relat_1 @ sk_C @ sk_B )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['126','129'])).

thf('131',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['98','130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YN2M3MlwdH
% 0.15/0.37  % Computer   : n001.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 10:34:29 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.61/0.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.61/0.79  % Solved by: fo/fo7.sh
% 0.61/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.79  % done 619 iterations in 0.310s
% 0.61/0.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.61/0.79  % SZS output start Refutation
% 0.61/0.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.61/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.79  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.61/0.79  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.61/0.79  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.61/0.79  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.61/0.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.61/0.79  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.61/0.79  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.61/0.79  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.61/0.79  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.61/0.79  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.61/0.79  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.61/0.79  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.61/0.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.79  thf(sk_C_type, type, sk_C: $i).
% 0.61/0.79  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.61/0.79  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.61/0.79  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.61/0.79  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.61/0.79  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.61/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.61/0.79  thf(d10_xboole_0, axiom,
% 0.61/0.79    (![A:$i,B:$i]:
% 0.61/0.79     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.61/0.79  thf('0', plain,
% 0.61/0.79      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.61/0.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.61/0.79  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.61/0.79      inference('simplify', [status(thm)], ['0'])).
% 0.61/0.79  thf(t146_funct_1, axiom,
% 0.61/0.79    (![A:$i,B:$i]:
% 0.61/0.79     ( ( v1_relat_1 @ B ) =>
% 0.61/0.79       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.61/0.79         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.61/0.79  thf('2', plain,
% 0.61/0.79      (![X30 : $i, X31 : $i]:
% 0.61/0.79         (~ (r1_tarski @ X30 @ (k1_relat_1 @ X31))
% 0.61/0.79          | (r1_tarski @ X30 @ (k10_relat_1 @ X31 @ (k9_relat_1 @ X31 @ X30)))
% 0.61/0.79          | ~ (v1_relat_1 @ X31))),
% 0.61/0.79      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.61/0.79  thf('3', plain,
% 0.61/0.79      (![X0 : $i]:
% 0.61/0.79         (~ (v1_relat_1 @ X0)
% 0.61/0.79          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.61/0.79             (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 0.61/0.79      inference('sup-', [status(thm)], ['1', '2'])).
% 0.61/0.79  thf(t168_relat_1, axiom,
% 0.61/0.79    (![A:$i,B:$i]:
% 0.61/0.79     ( ( v1_relat_1 @ B ) =>
% 0.61/0.79       ( ( k10_relat_1 @ B @ A ) =
% 0.61/0.79         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 0.61/0.79  thf('4', plain,
% 0.61/0.79      (![X16 : $i, X17 : $i]:
% 0.61/0.79         (((k10_relat_1 @ X16 @ X17)
% 0.61/0.79            = (k10_relat_1 @ X16 @ (k3_xboole_0 @ (k2_relat_1 @ X16) @ X17)))
% 0.61/0.79          | ~ (v1_relat_1 @ X16))),
% 0.61/0.79      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.61/0.79  thf(t167_relat_1, axiom,
% 0.61/0.79    (![A:$i,B:$i]:
% 0.61/0.79     ( ( v1_relat_1 @ B ) =>
% 0.61/0.79       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.61/0.79  thf('5', plain,
% 0.61/0.79      (![X14 : $i, X15 : $i]:
% 0.61/0.79         ((r1_tarski @ (k10_relat_1 @ X14 @ X15) @ (k1_relat_1 @ X14))
% 0.61/0.79          | ~ (v1_relat_1 @ X14))),
% 0.61/0.79      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.61/0.79  thf(t71_relat_1, axiom,
% 0.61/0.79    (![A:$i]:
% 0.61/0.79     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.61/0.79       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.61/0.79  thf('6', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.61/0.79      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.61/0.79  thf(d18_relat_1, axiom,
% 0.61/0.79    (![A:$i,B:$i]:
% 0.61/0.79     ( ( v1_relat_1 @ B ) =>
% 0.61/0.79       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.61/0.79  thf('7', plain,
% 0.61/0.79      (![X6 : $i, X7 : $i]:
% 0.61/0.79         (~ (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 0.61/0.79          | (v4_relat_1 @ X6 @ X7)
% 0.61/0.79          | ~ (v1_relat_1 @ X6))),
% 0.61/0.79      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.61/0.79  thf('8', plain,
% 0.61/0.79      (![X0 : $i, X1 : $i]:
% 0.61/0.79         (~ (r1_tarski @ X0 @ X1)
% 0.61/0.79          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.61/0.79          | (v4_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.61/0.79      inference('sup-', [status(thm)], ['6', '7'])).
% 0.61/0.79  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.61/0.79  thf('9', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.61/0.79      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.61/0.79  thf('10', plain,
% 0.61/0.79      (![X0 : $i, X1 : $i]:
% 0.61/0.79         (~ (r1_tarski @ X0 @ X1) | (v4_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.61/0.79      inference('demod', [status(thm)], ['8', '9'])).
% 0.61/0.79  thf('11', plain,
% 0.61/0.79      (![X0 : $i, X1 : $i]:
% 0.61/0.79         (~ (v1_relat_1 @ X0)
% 0.61/0.79          | (v4_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ X0 @ X1)) @ 
% 0.61/0.79             (k1_relat_1 @ X0)))),
% 0.61/0.79      inference('sup-', [status(thm)], ['5', '10'])).
% 0.61/0.79  thf(t38_relset_1, conjecture,
% 0.61/0.79    (![A:$i,B:$i,C:$i]:
% 0.61/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.79       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.61/0.79         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.61/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.79    (~( ![A:$i,B:$i,C:$i]:
% 0.61/0.79        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.79          ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.61/0.79            ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) )),
% 0.61/0.79    inference('cnf.neg', [status(esa)], [t38_relset_1])).
% 0.61/0.79  thf('12', plain,
% 0.61/0.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.61/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.79  thf(cc2_relset_1, axiom,
% 0.61/0.79    (![A:$i,B:$i,C:$i]:
% 0.61/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.79       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.61/0.79  thf('13', plain,
% 0.61/0.79      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.61/0.79         ((v4_relat_1 @ X37 @ X38)
% 0.61/0.79          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.61/0.79      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.61/0.79  thf('14', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.61/0.79      inference('sup-', [status(thm)], ['12', '13'])).
% 0.61/0.79  thf('15', plain,
% 0.61/0.79      (![X6 : $i, X7 : $i]:
% 0.61/0.79         (~ (v4_relat_1 @ X6 @ X7)
% 0.61/0.79          | (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 0.61/0.79          | ~ (v1_relat_1 @ X6))),
% 0.61/0.79      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.61/0.79  thf('16', plain,
% 0.61/0.79      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.61/0.79      inference('sup-', [status(thm)], ['14', '15'])).
% 0.61/0.79  thf('17', plain,
% 0.61/0.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.61/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.79  thf(cc1_relset_1, axiom,
% 0.61/0.79    (![A:$i,B:$i,C:$i]:
% 0.61/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.79       ( v1_relat_1 @ C ) ))).
% 0.61/0.79  thf('18', plain,
% 0.61/0.79      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.61/0.79         ((v1_relat_1 @ X34)
% 0.61/0.79          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.61/0.79      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.61/0.79  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 0.61/0.79      inference('sup-', [status(thm)], ['17', '18'])).
% 0.61/0.79  thf('20', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.61/0.79      inference('demod', [status(thm)], ['16', '19'])).
% 0.61/0.79  thf(t217_relat_1, axiom,
% 0.61/0.79    (![A:$i,B:$i]:
% 0.61/0.79     ( ( r1_tarski @ A @ B ) =>
% 0.61/0.79       ( ![C:$i]:
% 0.61/0.79         ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ A ) ) =>
% 0.61/0.79           ( v4_relat_1 @ C @ B ) ) ) ))).
% 0.61/0.79  thf('21', plain,
% 0.61/0.79      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.61/0.79         (~ (v1_relat_1 @ X20)
% 0.61/0.79          | ~ (v4_relat_1 @ X20 @ X21)
% 0.61/0.79          | (v4_relat_1 @ X20 @ X22)
% 0.61/0.79          | ~ (r1_tarski @ X21 @ X22))),
% 0.61/0.79      inference('cnf', [status(esa)], [t217_relat_1])).
% 0.61/0.79  thf('22', plain,
% 0.61/0.79      (![X0 : $i]:
% 0.61/0.79         ((v4_relat_1 @ X0 @ sk_A)
% 0.61/0.79          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ sk_C))
% 0.61/0.79          | ~ (v1_relat_1 @ X0))),
% 0.61/0.79      inference('sup-', [status(thm)], ['20', '21'])).
% 0.61/0.79  thf('23', plain,
% 0.61/0.79      (![X0 : $i]:
% 0.61/0.79         (~ (v1_relat_1 @ sk_C)
% 0.61/0.79          | ~ (v1_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_C @ X0)))
% 0.61/0.79          | (v4_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_C @ X0)) @ sk_A))),
% 0.61/0.79      inference('sup-', [status(thm)], ['11', '22'])).
% 0.61/0.79  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 0.61/0.79      inference('sup-', [status(thm)], ['17', '18'])).
% 0.61/0.79  thf('25', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.61/0.79      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.61/0.79  thf('26', plain,
% 0.61/0.79      (![X0 : $i]:
% 0.61/0.79         (v4_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_C @ X0)) @ sk_A)),
% 0.61/0.79      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.61/0.79  thf(t209_relat_1, axiom,
% 0.61/0.79    (![A:$i,B:$i]:
% 0.61/0.79     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.61/0.79       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.61/0.79  thf('27', plain,
% 0.61/0.79      (![X18 : $i, X19 : $i]:
% 0.61/0.79         (((X18) = (k7_relat_1 @ X18 @ X19))
% 0.61/0.79          | ~ (v4_relat_1 @ X18 @ X19)
% 0.61/0.79          | ~ (v1_relat_1 @ X18))),
% 0.61/0.79      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.61/0.79  thf('28', plain,
% 0.61/0.79      (![X0 : $i]:
% 0.61/0.79         (~ (v1_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_C @ X0)))
% 0.61/0.79          | ((k6_relat_1 @ (k10_relat_1 @ sk_C @ X0))
% 0.61/0.79              = (k7_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_C @ X0)) @ sk_A)))),
% 0.61/0.79      inference('sup-', [status(thm)], ['26', '27'])).
% 0.61/0.79  thf('29', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.61/0.79      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.61/0.79  thf('30', plain,
% 0.61/0.79      (![X0 : $i]:
% 0.61/0.79         ((k6_relat_1 @ (k10_relat_1 @ sk_C @ X0))
% 0.61/0.79           = (k7_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_C @ X0)) @ sk_A))),
% 0.61/0.79      inference('demod', [status(thm)], ['28', '29'])).
% 0.61/0.79  thf(t148_relat_1, axiom,
% 0.61/0.79    (![A:$i,B:$i]:
% 0.61/0.79     ( ( v1_relat_1 @ B ) =>
% 0.61/0.79       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.61/0.79  thf('31', plain,
% 0.61/0.79      (![X12 : $i, X13 : $i]:
% 0.61/0.79         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 0.61/0.79          | ~ (v1_relat_1 @ X12))),
% 0.61/0.79      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.61/0.79  thf('32', plain,
% 0.61/0.79      (![X0 : $i]:
% 0.61/0.79         (((k2_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_C @ X0)))
% 0.61/0.79            = (k9_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_C @ X0)) @ sk_A))
% 0.61/0.79          | ~ (v1_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_C @ X0))))),
% 0.61/0.79      inference('sup+', [status(thm)], ['30', '31'])).
% 0.61/0.79  thf('33', plain, (![X24 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 0.61/0.79      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.61/0.79  thf('34', plain,
% 0.61/0.79      (![X12 : $i, X13 : $i]:
% 0.61/0.79         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 0.61/0.79          | ~ (v1_relat_1 @ X12))),
% 0.61/0.79      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.61/0.79  thf(t43_funct_1, axiom,
% 0.61/0.79    (![A:$i,B:$i]:
% 0.61/0.79     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.61/0.79       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.61/0.79  thf('35', plain,
% 0.61/0.79      (![X32 : $i, X33 : $i]:
% 0.61/0.79         ((k5_relat_1 @ (k6_relat_1 @ X33) @ (k6_relat_1 @ X32))
% 0.61/0.79           = (k6_relat_1 @ (k3_xboole_0 @ X32 @ X33)))),
% 0.61/0.79      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.61/0.79  thf(t94_relat_1, axiom,
% 0.61/0.79    (![A:$i,B:$i]:
% 0.61/0.79     ( ( v1_relat_1 @ B ) =>
% 0.61/0.79       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.61/0.79  thf('36', plain,
% 0.61/0.79      (![X25 : $i, X26 : $i]:
% 0.61/0.79         (((k7_relat_1 @ X26 @ X25) = (k5_relat_1 @ (k6_relat_1 @ X25) @ X26))
% 0.61/0.79          | ~ (v1_relat_1 @ X26))),
% 0.61/0.79      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.61/0.79  thf('37', plain,
% 0.61/0.79      (![X0 : $i, X1 : $i]:
% 0.61/0.79         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.61/0.79            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.61/0.79          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.61/0.79      inference('sup+', [status(thm)], ['35', '36'])).
% 0.61/0.79  thf('38', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.61/0.79      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.61/0.79  thf('39', plain,
% 0.61/0.79      (![X0 : $i, X1 : $i]:
% 0.61/0.79         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.61/0.79           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.61/0.79      inference('demod', [status(thm)], ['37', '38'])).
% 0.61/0.79  thf('40', plain, (![X24 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 0.61/0.79      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.61/0.79  thf('41', plain,
% 0.61/0.79      (![X0 : $i, X1 : $i]:
% 0.61/0.79         ((k2_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.61/0.79           = (k3_xboole_0 @ X1 @ X0))),
% 0.61/0.79      inference('sup+', [status(thm)], ['39', '40'])).
% 0.61/0.79  thf('42', plain,
% 0.61/0.79      (![X0 : $i, X1 : $i]:
% 0.61/0.79         (((k9_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X1 @ X0))
% 0.61/0.79          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.61/0.79      inference('sup+', [status(thm)], ['34', '41'])).
% 0.61/0.79  thf('43', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.61/0.79      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.61/0.79  thf('44', plain,
% 0.61/0.79      (![X0 : $i, X1 : $i]:
% 0.61/0.79         ((k9_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.61/0.79      inference('demod', [status(thm)], ['42', '43'])).
% 0.61/0.79  thf('45', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.61/0.79      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.61/0.79  thf('46', plain,
% 0.61/0.79      (![X0 : $i]:
% 0.61/0.79         ((k10_relat_1 @ sk_C @ X0)
% 0.61/0.79           = (k3_xboole_0 @ (k10_relat_1 @ sk_C @ X0) @ sk_A))),
% 0.61/0.79      inference('demod', [status(thm)], ['32', '33', '44', '45'])).
% 0.61/0.79  thf('47', plain,
% 0.61/0.79      (![X0 : $i]:
% 0.61/0.79         (((k10_relat_1 @ sk_C @ (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ X0))
% 0.61/0.79            = (k3_xboole_0 @ (k10_relat_1 @ sk_C @ X0) @ sk_A))
% 0.61/0.79          | ~ (v1_relat_1 @ sk_C))),
% 0.61/0.79      inference('sup+', [status(thm)], ['4', '46'])).
% 0.61/0.79  thf('48', plain,
% 0.61/0.79      (![X0 : $i]:
% 0.61/0.79         ((k10_relat_1 @ sk_C @ X0)
% 0.61/0.79           = (k3_xboole_0 @ (k10_relat_1 @ sk_C @ X0) @ sk_A))),
% 0.61/0.79      inference('demod', [status(thm)], ['32', '33', '44', '45'])).
% 0.61/0.79  thf('49', plain, ((v1_relat_1 @ sk_C)),
% 0.61/0.79      inference('sup-', [status(thm)], ['17', '18'])).
% 0.61/0.79  thf('50', plain,
% 0.61/0.80      (![X0 : $i]:
% 0.61/0.80         ((k10_relat_1 @ sk_C @ (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ X0))
% 0.61/0.80           = (k10_relat_1 @ sk_C @ X0))),
% 0.61/0.80      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.61/0.80  thf('51', plain,
% 0.61/0.80      (![X14 : $i, X15 : $i]:
% 0.61/0.80         ((r1_tarski @ (k10_relat_1 @ X14 @ X15) @ (k1_relat_1 @ X14))
% 0.61/0.80          | ~ (v1_relat_1 @ X14))),
% 0.61/0.80      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.61/0.80  thf('52', plain,
% 0.61/0.80      (![X0 : $i, X2 : $i]:
% 0.61/0.80         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.61/0.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.61/0.80  thf('53', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (~ (v1_relat_1 @ X0)
% 0.61/0.80          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.61/0.80          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['51', '52'])).
% 0.61/0.80  thf('54', plain,
% 0.61/0.80      (![X0 : $i]:
% 0.61/0.80         (~ (r1_tarski @ (k1_relat_1 @ sk_C) @ (k10_relat_1 @ sk_C @ X0))
% 0.61/0.80          | ((k1_relat_1 @ sk_C)
% 0.61/0.80              = (k10_relat_1 @ sk_C @ (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ X0)))
% 0.61/0.80          | ~ (v1_relat_1 @ sk_C))),
% 0.61/0.80      inference('sup-', [status(thm)], ['50', '53'])).
% 0.61/0.80  thf('55', plain,
% 0.61/0.80      (![X0 : $i]:
% 0.61/0.80         ((k10_relat_1 @ sk_C @ (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ X0))
% 0.61/0.80           = (k10_relat_1 @ sk_C @ X0))),
% 0.61/0.80      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.61/0.80  thf('56', plain, ((v1_relat_1 @ sk_C)),
% 0.61/0.80      inference('sup-', [status(thm)], ['17', '18'])).
% 0.61/0.80  thf('57', plain,
% 0.61/0.80      (![X0 : $i]:
% 0.61/0.80         (~ (r1_tarski @ (k1_relat_1 @ sk_C) @ (k10_relat_1 @ sk_C @ X0))
% 0.61/0.80          | ((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ X0)))),
% 0.61/0.80      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.61/0.80  thf('58', plain,
% 0.61/0.80      ((~ (v1_relat_1 @ sk_C)
% 0.61/0.80        | ((k1_relat_1 @ sk_C)
% 0.61/0.80            = (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))))),
% 0.61/0.80      inference('sup-', [status(thm)], ['3', '57'])).
% 0.61/0.80  thf('59', plain, ((v1_relat_1 @ sk_C)),
% 0.61/0.80      inference('sup-', [status(thm)], ['17', '18'])).
% 0.61/0.80  thf('60', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.61/0.80      inference('simplify', [status(thm)], ['0'])).
% 0.61/0.80  thf('61', plain,
% 0.61/0.80      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf(t13_relset_1, axiom,
% 0.61/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.80     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.61/0.80       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.61/0.80         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.61/0.80  thf('62', plain,
% 0.61/0.80      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 0.61/0.80         (~ (r1_tarski @ (k1_relat_1 @ X54) @ X55)
% 0.61/0.80          | (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X56)))
% 0.61/0.80          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X56))))),
% 0.61/0.80      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.61/0.80  thf('63', plain,
% 0.61/0.80      (![X0 : $i]:
% 0.61/0.80         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.61/0.80          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.61/0.80      inference('sup-', [status(thm)], ['61', '62'])).
% 0.61/0.80  thf('64', plain,
% 0.61/0.80      ((m1_subset_1 @ sk_C @ 
% 0.61/0.80        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['60', '63'])).
% 0.61/0.80  thf('65', plain,
% 0.61/0.80      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.61/0.80         ((v4_relat_1 @ X37 @ X38)
% 0.61/0.80          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.61/0.80      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.61/0.80  thf('66', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.61/0.80      inference('sup-', [status(thm)], ['64', '65'])).
% 0.61/0.80  thf('67', plain,
% 0.61/0.80      (![X18 : $i, X19 : $i]:
% 0.61/0.80         (((X18) = (k7_relat_1 @ X18 @ X19))
% 0.61/0.80          | ~ (v4_relat_1 @ X18 @ X19)
% 0.61/0.80          | ~ (v1_relat_1 @ X18))),
% 0.61/0.80      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.61/0.80  thf('68', plain,
% 0.61/0.80      ((~ (v1_relat_1 @ sk_C)
% 0.61/0.80        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))),
% 0.61/0.80      inference('sup-', [status(thm)], ['66', '67'])).
% 0.61/0.80  thf('69', plain, ((v1_relat_1 @ sk_C)),
% 0.61/0.80      inference('sup-', [status(thm)], ['17', '18'])).
% 0.61/0.80  thf('70', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.61/0.80      inference('demod', [status(thm)], ['68', '69'])).
% 0.61/0.80  thf('71', plain,
% 0.61/0.80      (![X12 : $i, X13 : $i]:
% 0.61/0.80         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 0.61/0.80          | ~ (v1_relat_1 @ X12))),
% 0.61/0.80      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.61/0.80  thf('72', plain,
% 0.61/0.80      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 0.61/0.80        | ~ (v1_relat_1 @ sk_C))),
% 0.61/0.80      inference('sup+', [status(thm)], ['70', '71'])).
% 0.61/0.80  thf('73', plain, ((v1_relat_1 @ sk_C)),
% 0.61/0.80      inference('sup-', [status(thm)], ['17', '18'])).
% 0.61/0.80  thf('74', plain,
% 0.61/0.80      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.61/0.80      inference('demod', [status(thm)], ['72', '73'])).
% 0.61/0.80  thf('75', plain,
% 0.61/0.80      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf('76', plain,
% 0.61/0.80      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.61/0.80         ((v5_relat_1 @ X37 @ X39)
% 0.61/0.80          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.61/0.80      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.61/0.80  thf('77', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.61/0.80      inference('sup-', [status(thm)], ['75', '76'])).
% 0.61/0.80  thf(d19_relat_1, axiom,
% 0.61/0.80    (![A:$i,B:$i]:
% 0.61/0.80     ( ( v1_relat_1 @ B ) =>
% 0.61/0.80       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.61/0.80  thf('78', plain,
% 0.61/0.80      (![X8 : $i, X9 : $i]:
% 0.61/0.80         (~ (v5_relat_1 @ X8 @ X9)
% 0.61/0.80          | (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 0.61/0.80          | ~ (v1_relat_1 @ X8))),
% 0.61/0.80      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.61/0.80  thf('79', plain,
% 0.61/0.80      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.61/0.80      inference('sup-', [status(thm)], ['77', '78'])).
% 0.61/0.80  thf('80', plain, ((v1_relat_1 @ sk_C)),
% 0.61/0.80      inference('sup-', [status(thm)], ['17', '18'])).
% 0.61/0.80  thf('81', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.61/0.80      inference('demod', [status(thm)], ['79', '80'])).
% 0.61/0.80  thf('82', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (~ (r1_tarski @ X0 @ X1) | (v4_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.61/0.80      inference('demod', [status(thm)], ['8', '9'])).
% 0.61/0.80  thf('83', plain, ((v4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B)),
% 0.61/0.80      inference('sup-', [status(thm)], ['81', '82'])).
% 0.61/0.80  thf('84', plain,
% 0.61/0.80      (![X18 : $i, X19 : $i]:
% 0.61/0.80         (((X18) = (k7_relat_1 @ X18 @ X19))
% 0.61/0.80          | ~ (v4_relat_1 @ X18 @ X19)
% 0.61/0.80          | ~ (v1_relat_1 @ X18))),
% 0.61/0.80      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.61/0.80  thf('85', plain,
% 0.61/0.80      ((~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.61/0.80        | ((k6_relat_1 @ (k2_relat_1 @ sk_C))
% 0.61/0.80            = (k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['83', '84'])).
% 0.61/0.80  thf('86', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.61/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.61/0.80  thf('87', plain,
% 0.61/0.80      (((k6_relat_1 @ (k2_relat_1 @ sk_C))
% 0.61/0.80         = (k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B))),
% 0.61/0.80      inference('demod', [status(thm)], ['85', '86'])).
% 0.61/0.80  thf('88', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.61/0.80           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.61/0.80      inference('demod', [status(thm)], ['37', '38'])).
% 0.61/0.80  thf('89', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.61/0.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.61/0.80  thf('90', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.61/0.80           = (k3_xboole_0 @ X1 @ X0))),
% 0.61/0.80      inference('sup+', [status(thm)], ['88', '89'])).
% 0.61/0.80  thf('91', plain,
% 0.61/0.80      (((k1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.61/0.80         = (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.61/0.80      inference('sup+', [status(thm)], ['87', '90'])).
% 0.61/0.80  thf('92', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.61/0.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.61/0.80  thf('93', plain,
% 0.61/0.80      (((k2_relat_1 @ sk_C) = (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.61/0.80      inference('demod', [status(thm)], ['91', '92'])).
% 0.61/0.80  thf('94', plain,
% 0.61/0.80      (![X16 : $i, X17 : $i]:
% 0.61/0.80         (((k10_relat_1 @ X16 @ X17)
% 0.61/0.80            = (k10_relat_1 @ X16 @ (k3_xboole_0 @ (k2_relat_1 @ X16) @ X17)))
% 0.61/0.80          | ~ (v1_relat_1 @ X16))),
% 0.61/0.80      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.61/0.80  thf('95', plain,
% 0.61/0.80      ((((k10_relat_1 @ sk_C @ sk_B)
% 0.61/0.80          = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.61/0.80        | ~ (v1_relat_1 @ sk_C))),
% 0.61/0.80      inference('sup+', [status(thm)], ['93', '94'])).
% 0.61/0.80  thf('96', plain, ((v1_relat_1 @ sk_C)),
% 0.61/0.80      inference('sup-', [status(thm)], ['17', '18'])).
% 0.61/0.80  thf('97', plain,
% 0.61/0.80      (((k10_relat_1 @ sk_C @ sk_B)
% 0.61/0.80         = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 0.61/0.80      inference('demod', [status(thm)], ['95', '96'])).
% 0.61/0.80  thf('98', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B))),
% 0.61/0.80      inference('demod', [status(thm)], ['58', '59', '74', '97'])).
% 0.61/0.80  thf('99', plain,
% 0.61/0.80      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.61/0.80          != (k2_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.61/0.80        | ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.61/0.80            != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf('100', plain,
% 0.61/0.80      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.61/0.80          != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.61/0.80         <= (~
% 0.61/0.80             (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.61/0.80                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.61/0.80      inference('split', [status(esa)], ['99'])).
% 0.61/0.80  thf('101', plain,
% 0.61/0.80      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf(redefinition_k1_relset_1, axiom,
% 0.61/0.80    (![A:$i,B:$i,C:$i]:
% 0.61/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.80       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.61/0.80  thf('102', plain,
% 0.61/0.80      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.61/0.80         (((k1_relset_1 @ X41 @ X42 @ X40) = (k1_relat_1 @ X40))
% 0.61/0.80          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 0.61/0.80      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.61/0.80  thf('103', plain,
% 0.61/0.80      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.61/0.80      inference('sup-', [status(thm)], ['101', '102'])).
% 0.61/0.80  thf('104', plain,
% 0.61/0.80      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) != (k1_relat_1 @ sk_C)))
% 0.61/0.80         <= (~
% 0.61/0.80             (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.61/0.80                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.61/0.80      inference('demod', [status(thm)], ['100', '103'])).
% 0.61/0.80  thf('105', plain,
% 0.61/0.80      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf(redefinition_k7_relset_1, axiom,
% 0.61/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.80       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.61/0.80  thf('106', plain,
% 0.61/0.80      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.61/0.80         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 0.61/0.80          | ((k7_relset_1 @ X47 @ X48 @ X46 @ X49) = (k9_relat_1 @ X46 @ X49)))),
% 0.61/0.80      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.61/0.80  thf('107', plain,
% 0.61/0.80      (![X0 : $i]:
% 0.61/0.80         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.61/0.80      inference('sup-', [status(thm)], ['105', '106'])).
% 0.61/0.80  thf('108', plain,
% 0.61/0.80      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.61/0.80          != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.61/0.80         <= (~
% 0.61/0.80             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.61/0.80                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.61/0.80      inference('split', [status(esa)], ['99'])).
% 0.61/0.80  thf('109', plain,
% 0.61/0.80      ((((k9_relat_1 @ sk_C @ sk_A) != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.61/0.80         <= (~
% 0.61/0.80             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.61/0.80                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.61/0.80      inference('sup-', [status(thm)], ['107', '108'])).
% 0.61/0.80  thf('110', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.61/0.80      inference('sup-', [status(thm)], ['12', '13'])).
% 0.61/0.80  thf('111', plain,
% 0.61/0.80      (![X18 : $i, X19 : $i]:
% 0.61/0.80         (((X18) = (k7_relat_1 @ X18 @ X19))
% 0.61/0.80          | ~ (v4_relat_1 @ X18 @ X19)
% 0.61/0.80          | ~ (v1_relat_1 @ X18))),
% 0.61/0.80      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.61/0.80  thf('112', plain,
% 0.61/0.80      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['110', '111'])).
% 0.61/0.80  thf('113', plain, ((v1_relat_1 @ sk_C)),
% 0.61/0.80      inference('sup-', [status(thm)], ['17', '18'])).
% 0.61/0.80  thf('114', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.61/0.80      inference('demod', [status(thm)], ['112', '113'])).
% 0.61/0.80  thf('115', plain,
% 0.61/0.80      (![X12 : $i, X13 : $i]:
% 0.61/0.80         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 0.61/0.80          | ~ (v1_relat_1 @ X12))),
% 0.61/0.80      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.61/0.80  thf('116', plain,
% 0.61/0.80      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 0.61/0.80        | ~ (v1_relat_1 @ sk_C))),
% 0.61/0.80      inference('sup+', [status(thm)], ['114', '115'])).
% 0.61/0.80  thf('117', plain, ((v1_relat_1 @ sk_C)),
% 0.61/0.80      inference('sup-', [status(thm)], ['17', '18'])).
% 0.61/0.80  thf('118', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.61/0.80      inference('demod', [status(thm)], ['116', '117'])).
% 0.61/0.80  thf('119', plain,
% 0.61/0.80      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf(redefinition_k2_relset_1, axiom,
% 0.61/0.80    (![A:$i,B:$i,C:$i]:
% 0.61/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.80       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.61/0.80  thf('120', plain,
% 0.61/0.80      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.61/0.80         (((k2_relset_1 @ X44 @ X45 @ X43) = (k2_relat_1 @ X43))
% 0.61/0.80          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45))))),
% 0.61/0.80      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.61/0.80  thf('121', plain,
% 0.61/0.80      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.61/0.80      inference('sup-', [status(thm)], ['119', '120'])).
% 0.61/0.80  thf('122', plain,
% 0.61/0.80      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.61/0.80         <= (~
% 0.61/0.80             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.61/0.80                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.61/0.80      inference('demod', [status(thm)], ['109', '118', '121'])).
% 0.61/0.80  thf('123', plain,
% 0.61/0.80      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.61/0.80          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.61/0.80      inference('simplify', [status(thm)], ['122'])).
% 0.61/0.80  thf('124', plain,
% 0.61/0.80      (~
% 0.61/0.80       (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.61/0.80          = (k1_relset_1 @ sk_A @ sk_B @ sk_C))) | 
% 0.61/0.80       ~
% 0.61/0.80       (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.61/0.80          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.61/0.80      inference('split', [status(esa)], ['99'])).
% 0.61/0.80  thf('125', plain,
% 0.61/0.80      (~
% 0.61/0.80       (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.61/0.80          = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.61/0.80      inference('sat_resolution*', [status(thm)], ['123', '124'])).
% 0.61/0.80  thf('126', plain,
% 0.61/0.80      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) != (k1_relat_1 @ sk_C))),
% 0.61/0.80      inference('simpl_trail', [status(thm)], ['104', '125'])).
% 0.61/0.80  thf('127', plain,
% 0.61/0.80      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf(redefinition_k8_relset_1, axiom,
% 0.61/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.80       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.61/0.80  thf('128', plain,
% 0.61/0.80      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.61/0.80         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 0.61/0.80          | ((k8_relset_1 @ X51 @ X52 @ X50 @ X53) = (k10_relat_1 @ X50 @ X53)))),
% 0.61/0.80      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.61/0.80  thf('129', plain,
% 0.61/0.80      (![X0 : $i]:
% 0.61/0.80         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.61/0.80      inference('sup-', [status(thm)], ['127', '128'])).
% 0.61/0.80  thf('130', plain, (((k10_relat_1 @ sk_C @ sk_B) != (k1_relat_1 @ sk_C))),
% 0.61/0.80      inference('demod', [status(thm)], ['126', '129'])).
% 0.61/0.80  thf('131', plain, ($false),
% 0.61/0.80      inference('simplify_reflect-', [status(thm)], ['98', '130'])).
% 0.61/0.80  
% 0.61/0.80  % SZS output end Refutation
% 0.61/0.80  
% 0.61/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
