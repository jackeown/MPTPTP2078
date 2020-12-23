%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.altlpMewuZ

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:41 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 161 expanded)
%              Number of leaves         :   46 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :  902 (1766 expanded)
%              Number of equality atoms :   72 ( 133 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relset_1_type,type,(
    k5_relset_1: $i > $i > $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(t124_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('0',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k8_relat_1 @ X13 @ X12 )
        = ( k3_xboole_0 @ X12 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X12 ) @ X13 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t124_relat_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k8_relat_1 @ X13 @ X12 )
        = ( k1_setfam_1 @ ( k2_tarski @ X12 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X12 ) @ X13 ) ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('3',plain,(
    ! [X22: $i] :
      ( ( ( k7_relat_1 @ X22 @ ( k1_relat_1 @ X22 ) )
        = X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

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

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t33_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( m1_subset_1 @ ( k5_relset_1 @ A @ C @ D @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('5',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( m1_subset_1 @ ( k5_relset_1 @ X47 @ X48 @ X49 @ X50 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[t33_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k5_relset_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k5_relset_1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('8',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( ( k5_relset_1 @ X36 @ X37 @ X35 @ X38 )
        = ( k7_relat_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_relset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k7_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('13',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('14',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_C @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) )
    = sk_C ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,
    ( ( ( k8_relat_1 @ sk_B @ sk_C )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['2','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('24',plain,
    ( ( k8_relat_1 @ sk_B @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('25',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k8_relat_1 @ X11 @ X10 )
        = ( k5_relat_1 @ X10 @ ( k6_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('26',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('27',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X17 @ X16 ) )
        = ( k10_relat_1 @ X17 @ ( k1_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('29',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['24','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('35',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('39',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('40',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('43',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( ( k7_relset_1 @ X40 @ X41 @ X39 @ X42 )
        = ( k9_relat_1 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['36'])).

thf('46',plain,
    ( ( ( k9_relat_1 @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('48',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('49',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('50',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18
        = ( k7_relat_1 @ X18 @ X19 ) )
      | ~ ( v4_relat_1 @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('53',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('54',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) )
        = ( k9_relat_1 @ X14 @ X15 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('55',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('59',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k2_relset_1 @ X33 @ X34 @ X32 )
        = ( k2_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('60',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['46','57','60'])).

thf('62',plain,
    ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['36'])).

thf('64',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
 != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['62','63'])).

thf('65',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['41','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('67',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( ( k8_relset_1 @ X44 @ X45 @ X43 @ X46 )
        = ( k10_relat_1 @ X43 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ( k10_relat_1 @ sk_C @ sk_B )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['65','68'])).

thf('70',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['35','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.altlpMewuZ
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:56:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.55  % Solved by: fo/fo7.sh
% 0.35/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.55  % done 92 iterations in 0.049s
% 0.35/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.55  % SZS output start Refutation
% 0.35/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.55  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.35/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.35/0.55  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.35/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.55  thf(k5_relset_1_type, type, k5_relset_1: $i > $i > $i > $i > $i).
% 0.35/0.55  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.35/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.35/0.55  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.35/0.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.35/0.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.35/0.55  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.35/0.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.35/0.55  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.35/0.55  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.35/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.35/0.55  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.35/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.55  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.35/0.55  thf(t124_relat_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( v1_relat_1 @ B ) =>
% 0.35/0.55       ( ( k8_relat_1 @ A @ B ) =
% 0.35/0.55         ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.35/0.55  thf('0', plain,
% 0.35/0.55      (![X12 : $i, X13 : $i]:
% 0.35/0.55         (((k8_relat_1 @ X13 @ X12)
% 0.35/0.55            = (k3_xboole_0 @ X12 @ (k2_zfmisc_1 @ (k1_relat_1 @ X12) @ X13)))
% 0.35/0.55          | ~ (v1_relat_1 @ X12))),
% 0.35/0.55      inference('cnf', [status(esa)], [t124_relat_1])).
% 0.35/0.55  thf(t12_setfam_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.35/0.55  thf('1', plain,
% 0.35/0.55      (![X4 : $i, X5 : $i]:
% 0.35/0.55         ((k1_setfam_1 @ (k2_tarski @ X4 @ X5)) = (k3_xboole_0 @ X4 @ X5))),
% 0.35/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.35/0.55  thf('2', plain,
% 0.35/0.55      (![X12 : $i, X13 : $i]:
% 0.35/0.55         (((k8_relat_1 @ X13 @ X12)
% 0.35/0.55            = (k1_setfam_1 @ 
% 0.35/0.55               (k2_tarski @ X12 @ (k2_zfmisc_1 @ (k1_relat_1 @ X12) @ X13))))
% 0.35/0.55          | ~ (v1_relat_1 @ X12))),
% 0.35/0.55      inference('demod', [status(thm)], ['0', '1'])).
% 0.35/0.55  thf(t98_relat_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( v1_relat_1 @ A ) =>
% 0.35/0.55       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.35/0.55  thf('3', plain,
% 0.35/0.55      (![X22 : $i]:
% 0.35/0.55         (((k7_relat_1 @ X22 @ (k1_relat_1 @ X22)) = (X22))
% 0.35/0.55          | ~ (v1_relat_1 @ X22))),
% 0.35/0.55      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.35/0.55  thf(t38_relset_1, conjecture,
% 0.35/0.55    (![A:$i,B:$i,C:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.55       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.35/0.55         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.35/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.35/0.55        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.55          ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.35/0.55            ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) )),
% 0.35/0.55    inference('cnf.neg', [status(esa)], [t38_relset_1])).
% 0.35/0.55  thf('4', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(t33_relset_1, axiom,
% 0.35/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.35/0.55       ( m1_subset_1 @
% 0.35/0.55         ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 0.35/0.55         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.35/0.55  thf('5', plain,
% 0.35/0.55      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.35/0.55         ((m1_subset_1 @ (k5_relset_1 @ X47 @ X48 @ X49 @ X50) @ 
% 0.35/0.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 0.35/0.55          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48))))),
% 0.35/0.55      inference('cnf', [status(esa)], [t33_relset_1])).
% 0.35/0.55  thf('6', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         (m1_subset_1 @ (k5_relset_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.35/0.55          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.35/0.55  thf('7', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(redefinition_k5_relset_1, axiom,
% 0.35/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.55       ( ( k5_relset_1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.35/0.55  thf('8', plain,
% 0.35/0.55      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.35/0.55          | ((k5_relset_1 @ X36 @ X37 @ X35 @ X38) = (k7_relat_1 @ X35 @ X38)))),
% 0.35/0.55      inference('cnf', [status(esa)], [redefinition_k5_relset_1])).
% 0.35/0.55  thf('9', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((k5_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k7_relat_1 @ sk_C @ X0))),
% 0.35/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.35/0.55  thf('10', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         (m1_subset_1 @ (k7_relat_1 @ sk_C @ X0) @ 
% 0.35/0.55          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 0.35/0.55      inference('demod', [status(thm)], ['6', '9'])).
% 0.35/0.55  thf('11', plain,
% 0.35/0.55      (((m1_subset_1 @ sk_C @ 
% 0.35/0.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))
% 0.35/0.55        | ~ (v1_relat_1 @ sk_C))),
% 0.35/0.55      inference('sup+', [status(thm)], ['3', '10'])).
% 0.35/0.55  thf('12', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(cc1_relset_1, axiom,
% 0.35/0.55    (![A:$i,B:$i,C:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.55       ( v1_relat_1 @ C ) ))).
% 0.35/0.55  thf('13', plain,
% 0.35/0.55      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.35/0.55         ((v1_relat_1 @ X23)
% 0.35/0.55          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.35/0.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.35/0.55  thf('14', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.35/0.55  thf('15', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C @ 
% 0.35/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))),
% 0.35/0.55      inference('demod', [status(thm)], ['11', '14'])).
% 0.35/0.55  thf(t3_subset, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.35/0.55  thf('16', plain,
% 0.35/0.55      (![X6 : $i, X7 : $i]:
% 0.35/0.55         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.35/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.35/0.55  thf('17', plain,
% 0.35/0.55      ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B))),
% 0.35/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.35/0.55  thf(t28_xboole_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.35/0.55  thf('18', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.35/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.35/0.55  thf('19', plain,
% 0.35/0.55      (![X4 : $i, X5 : $i]:
% 0.35/0.55         ((k1_setfam_1 @ (k2_tarski @ X4 @ X5)) = (k3_xboole_0 @ X4 @ X5))),
% 0.35/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.35/0.55  thf('20', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (((k1_setfam_1 @ (k2_tarski @ X0 @ X1)) = (X0))
% 0.35/0.55          | ~ (r1_tarski @ X0 @ X1))),
% 0.35/0.55      inference('demod', [status(thm)], ['18', '19'])).
% 0.35/0.55  thf('21', plain,
% 0.35/0.55      (((k1_setfam_1 @ 
% 0.35/0.55         (k2_tarski @ sk_C @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))
% 0.35/0.55         = (sk_C))),
% 0.35/0.55      inference('sup-', [status(thm)], ['17', '20'])).
% 0.35/0.55  thf('22', plain,
% 0.35/0.55      ((((k8_relat_1 @ sk_B @ sk_C) = (sk_C)) | ~ (v1_relat_1 @ sk_C))),
% 0.35/0.55      inference('sup+', [status(thm)], ['2', '21'])).
% 0.35/0.55  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.35/0.55  thf('24', plain, (((k8_relat_1 @ sk_B @ sk_C) = (sk_C))),
% 0.35/0.55      inference('demod', [status(thm)], ['22', '23'])).
% 0.35/0.55  thf(t123_relat_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( v1_relat_1 @ B ) =>
% 0.35/0.55       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.35/0.55  thf('25', plain,
% 0.35/0.55      (![X10 : $i, X11 : $i]:
% 0.35/0.55         (((k8_relat_1 @ X11 @ X10) = (k5_relat_1 @ X10 @ (k6_relat_1 @ X11)))
% 0.35/0.55          | ~ (v1_relat_1 @ X10))),
% 0.35/0.55      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.35/0.55  thf(t71_relat_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.35/0.55       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.35/0.55  thf('26', plain, (![X20 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 0.35/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.35/0.55  thf(t182_relat_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( v1_relat_1 @ A ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( v1_relat_1 @ B ) =>
% 0.35/0.55           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.35/0.55             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.35/0.55  thf('27', plain,
% 0.35/0.55      (![X16 : $i, X17 : $i]:
% 0.35/0.55         (~ (v1_relat_1 @ X16)
% 0.35/0.55          | ((k1_relat_1 @ (k5_relat_1 @ X17 @ X16))
% 0.35/0.55              = (k10_relat_1 @ X17 @ (k1_relat_1 @ X16)))
% 0.35/0.55          | ~ (v1_relat_1 @ X17))),
% 0.35/0.55      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.35/0.55  thf('28', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.35/0.55            = (k10_relat_1 @ X1 @ X0))
% 0.35/0.55          | ~ (v1_relat_1 @ X1)
% 0.35/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.35/0.55      inference('sup+', [status(thm)], ['26', '27'])).
% 0.35/0.55  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.35/0.55  thf('29', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.35/0.55      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.35/0.55  thf('30', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.35/0.55            = (k10_relat_1 @ X1 @ X0))
% 0.35/0.55          | ~ (v1_relat_1 @ X1))),
% 0.35/0.55      inference('demod', [status(thm)], ['28', '29'])).
% 0.35/0.55  thf('31', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (((k1_relat_1 @ (k8_relat_1 @ X1 @ X0)) = (k10_relat_1 @ X0 @ X1))
% 0.35/0.55          | ~ (v1_relat_1 @ X0)
% 0.35/0.55          | ~ (v1_relat_1 @ X0))),
% 0.35/0.55      inference('sup+', [status(thm)], ['25', '30'])).
% 0.35/0.55  thf('32', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (~ (v1_relat_1 @ X0)
% 0.35/0.55          | ((k1_relat_1 @ (k8_relat_1 @ X1 @ X0)) = (k10_relat_1 @ X0 @ X1)))),
% 0.35/0.55      inference('simplify', [status(thm)], ['31'])).
% 0.35/0.55  thf('33', plain,
% 0.35/0.55      ((((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B))
% 0.35/0.55        | ~ (v1_relat_1 @ sk_C))),
% 0.35/0.55      inference('sup+', [status(thm)], ['24', '32'])).
% 0.35/0.55  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.35/0.55  thf('35', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B))),
% 0.35/0.55      inference('demod', [status(thm)], ['33', '34'])).
% 0.35/0.55  thf('36', plain,
% 0.35/0.55      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.35/0.55          != (k2_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.35/0.55        | ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.35/0.55            != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('37', plain,
% 0.35/0.55      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.35/0.55          != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.35/0.55         <= (~
% 0.35/0.55             (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.35/0.55                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.35/0.55      inference('split', [status(esa)], ['36'])).
% 0.35/0.55  thf('38', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(redefinition_k1_relset_1, axiom,
% 0.35/0.55    (![A:$i,B:$i,C:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.55       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.35/0.55  thf('39', plain,
% 0.35/0.55      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.35/0.55         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 0.35/0.55          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.35/0.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.35/0.55  thf('40', plain,
% 0.35/0.55      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.35/0.55      inference('sup-', [status(thm)], ['38', '39'])).
% 0.35/0.55  thf('41', plain,
% 0.35/0.55      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) != (k1_relat_1 @ sk_C)))
% 0.35/0.55         <= (~
% 0.35/0.55             (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.35/0.55                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.35/0.55      inference('demod', [status(thm)], ['37', '40'])).
% 0.35/0.55  thf('42', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(redefinition_k7_relset_1, axiom,
% 0.35/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.55       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.35/0.55  thf('43', plain,
% 0.35/0.55      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.35/0.55          | ((k7_relset_1 @ X40 @ X41 @ X39 @ X42) = (k9_relat_1 @ X39 @ X42)))),
% 0.35/0.55      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.35/0.55  thf('44', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.35/0.55      inference('sup-', [status(thm)], ['42', '43'])).
% 0.35/0.55  thf('45', plain,
% 0.35/0.55      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.35/0.55          != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.35/0.55         <= (~
% 0.35/0.55             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.35/0.55                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.35/0.55      inference('split', [status(esa)], ['36'])).
% 0.35/0.55  thf('46', plain,
% 0.35/0.55      ((((k9_relat_1 @ sk_C @ sk_A) != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.35/0.55         <= (~
% 0.35/0.55             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.35/0.55                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.35/0.55      inference('sup-', [status(thm)], ['44', '45'])).
% 0.35/0.55  thf('47', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(cc2_relset_1, axiom,
% 0.35/0.55    (![A:$i,B:$i,C:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.55       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.35/0.55  thf('48', plain,
% 0.35/0.55      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.35/0.55         ((v4_relat_1 @ X26 @ X27)
% 0.35/0.55          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.35/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.35/0.55  thf('49', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.35/0.55      inference('sup-', [status(thm)], ['47', '48'])).
% 0.35/0.55  thf(t209_relat_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.35/0.55       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.35/0.55  thf('50', plain,
% 0.35/0.55      (![X18 : $i, X19 : $i]:
% 0.35/0.55         (((X18) = (k7_relat_1 @ X18 @ X19))
% 0.35/0.55          | ~ (v4_relat_1 @ X18 @ X19)
% 0.35/0.55          | ~ (v1_relat_1 @ X18))),
% 0.35/0.55      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.35/0.55  thf('51', plain,
% 0.35/0.55      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['49', '50'])).
% 0.35/0.55  thf('52', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.35/0.55  thf('53', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['51', '52'])).
% 0.35/0.55  thf(t148_relat_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( v1_relat_1 @ B ) =>
% 0.35/0.55       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.35/0.55  thf('54', plain,
% 0.35/0.55      (![X14 : $i, X15 : $i]:
% 0.35/0.55         (((k2_relat_1 @ (k7_relat_1 @ X14 @ X15)) = (k9_relat_1 @ X14 @ X15))
% 0.35/0.55          | ~ (v1_relat_1 @ X14))),
% 0.35/0.55      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.35/0.55  thf('55', plain,
% 0.35/0.55      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 0.35/0.55        | ~ (v1_relat_1 @ sk_C))),
% 0.35/0.55      inference('sup+', [status(thm)], ['53', '54'])).
% 0.35/0.55  thf('56', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.35/0.55  thf('57', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['55', '56'])).
% 0.35/0.55  thf('58', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(redefinition_k2_relset_1, axiom,
% 0.35/0.55    (![A:$i,B:$i,C:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.55       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.35/0.55  thf('59', plain,
% 0.35/0.55      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.35/0.55         (((k2_relset_1 @ X33 @ X34 @ X32) = (k2_relat_1 @ X32))
% 0.35/0.55          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.35/0.55      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.35/0.55  thf('60', plain,
% 0.35/0.55      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.35/0.55      inference('sup-', [status(thm)], ['58', '59'])).
% 0.35/0.55  thf('61', plain,
% 0.35/0.55      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.35/0.55         <= (~
% 0.35/0.55             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.35/0.55                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.35/0.55      inference('demod', [status(thm)], ['46', '57', '60'])).
% 0.35/0.55  thf('62', plain,
% 0.35/0.55      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.35/0.55          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.35/0.55      inference('simplify', [status(thm)], ['61'])).
% 0.35/0.55  thf('63', plain,
% 0.35/0.55      (~
% 0.35/0.55       (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.35/0.55          = (k1_relset_1 @ sk_A @ sk_B @ sk_C))) | 
% 0.35/0.55       ~
% 0.35/0.55       (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.35/0.55          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.35/0.55      inference('split', [status(esa)], ['36'])).
% 0.35/0.55  thf('64', plain,
% 0.35/0.55      (~
% 0.35/0.55       (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.35/0.55          = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.35/0.55      inference('sat_resolution*', [status(thm)], ['62', '63'])).
% 0.35/0.55  thf('65', plain,
% 0.35/0.55      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) != (k1_relat_1 @ sk_C))),
% 0.35/0.55      inference('simpl_trail', [status(thm)], ['41', '64'])).
% 0.35/0.55  thf('66', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(redefinition_k8_relset_1, axiom,
% 0.35/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.55       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.35/0.55  thf('67', plain,
% 0.35/0.55      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 0.35/0.55          | ((k8_relset_1 @ X44 @ X45 @ X43 @ X46) = (k10_relat_1 @ X43 @ X46)))),
% 0.35/0.55      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.35/0.55  thf('68', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.35/0.55      inference('sup-', [status(thm)], ['66', '67'])).
% 0.35/0.55  thf('69', plain, (((k10_relat_1 @ sk_C @ sk_B) != (k1_relat_1 @ sk_C))),
% 0.35/0.55      inference('demod', [status(thm)], ['65', '68'])).
% 0.35/0.55  thf('70', plain, ($false),
% 0.35/0.55      inference('simplify_reflect-', [status(thm)], ['35', '69'])).
% 0.35/0.55  
% 0.35/0.55  % SZS output end Refutation
% 0.35/0.55  
% 0.35/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
