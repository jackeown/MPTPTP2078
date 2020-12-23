%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kwETqZjDTl

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:54 EST 2020

% Result     : Theorem 2.09s
% Output     : Refutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 106 expanded)
%              Number of leaves         :   31 (  44 expanded)
%              Depth                    :   16
%              Number of atoms          :  485 ( 725 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t19_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t19_relset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('3',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X32 @ X33 @ X34 ) @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('4',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('6',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k2_relset_1 @ X36 @ X37 @ X35 )
        = ( k2_relat_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('9',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['6','9'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X12 @ X11 )
      | ( r1_tarski @ ( k2_xboole_0 @ X10 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X1 ) @ ( k2_xboole_0 @ X0 @ sk_B ) )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('16',plain,(
    ! [X22: $i] :
      ( ( ( k3_relat_1 @ X22 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X22 ) @ ( k2_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v4_relat_1 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('20',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X25
        = ( k7_relat_1 @ X25 @ X26 ) )
      | ~ ( v4_relat_1 @ X25 @ X26 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( v1_relat_1 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('26',plain,(
    ! [X23: $i,X24: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['22','27'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('29',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X27 @ X28 ) ) @ X28 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('30',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['25','26'])).

thf('32',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X12 @ X11 )
      | ( r1_tarski @ ( k2_xboole_0 @ X10 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ X1 ) @ ( k2_xboole_0 @ X0 @ sk_A ) )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ X0 ) @ ( k2_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','36'])).

thf('38',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['16','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['25','26'])).

thf('40',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('41',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('42',plain,
    ( ( k2_xboole_0 @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_A ) )
    = ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('43',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_A ) @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['0','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kwETqZjDTl
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:06:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.09/2.26  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.09/2.26  % Solved by: fo/fo7.sh
% 2.09/2.26  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.09/2.26  % done 2973 iterations in 1.806s
% 2.09/2.26  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.09/2.26  % SZS output start Refutation
% 2.09/2.26  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.09/2.26  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.09/2.26  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.09/2.26  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.09/2.26  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.09/2.26  thf(sk_C_type, type, sk_C: $i).
% 2.09/2.26  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.09/2.26  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.09/2.26  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.09/2.26  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.09/2.26  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.09/2.26  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.09/2.26  thf(sk_B_type, type, sk_B: $i).
% 2.09/2.26  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 2.09/2.26  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.09/2.26  thf(sk_A_type, type, sk_A: $i).
% 2.09/2.26  thf(t19_relset_1, conjecture,
% 2.09/2.26    (![A:$i,B:$i,C:$i]:
% 2.09/2.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.09/2.26       ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 2.09/2.26  thf(zf_stmt_0, negated_conjecture,
% 2.09/2.26    (~( ![A:$i,B:$i,C:$i]:
% 2.09/2.26        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.09/2.26          ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 2.09/2.26    inference('cnf.neg', [status(esa)], [t19_relset_1])).
% 2.09/2.26  thf('0', plain,
% 2.09/2.26      (~ (r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 2.09/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.26  thf(t7_xboole_1, axiom,
% 2.09/2.26    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.09/2.26  thf('1', plain,
% 2.09/2.26      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 2.09/2.26      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.09/2.26  thf('2', plain,
% 2.09/2.26      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.09/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.26  thf(dt_k2_relset_1, axiom,
% 2.09/2.26    (![A:$i,B:$i,C:$i]:
% 2.09/2.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.09/2.26       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 2.09/2.26  thf('3', plain,
% 2.09/2.26      (![X32 : $i, X33 : $i, X34 : $i]:
% 2.09/2.26         ((m1_subset_1 @ (k2_relset_1 @ X32 @ X33 @ X34) @ (k1_zfmisc_1 @ X33))
% 2.09/2.26          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 2.09/2.26      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 2.09/2.26  thf('4', plain,
% 2.09/2.26      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 2.09/2.26      inference('sup-', [status(thm)], ['2', '3'])).
% 2.09/2.26  thf(t3_subset, axiom,
% 2.09/2.26    (![A:$i,B:$i]:
% 2.09/2.26     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.09/2.26  thf('5', plain,
% 2.09/2.26      (![X17 : $i, X18 : $i]:
% 2.09/2.26         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 2.09/2.26      inference('cnf', [status(esa)], [t3_subset])).
% 2.09/2.26  thf('6', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_C) @ sk_B)),
% 2.09/2.26      inference('sup-', [status(thm)], ['4', '5'])).
% 2.09/2.26  thf('7', plain,
% 2.09/2.26      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.09/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.26  thf(redefinition_k2_relset_1, axiom,
% 2.09/2.26    (![A:$i,B:$i,C:$i]:
% 2.09/2.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.09/2.26       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.09/2.26  thf('8', plain,
% 2.09/2.26      (![X35 : $i, X36 : $i, X37 : $i]:
% 2.09/2.26         (((k2_relset_1 @ X36 @ X37 @ X35) = (k2_relat_1 @ X35))
% 2.09/2.26          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 2.09/2.26      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.09/2.26  thf('9', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 2.09/2.26      inference('sup-', [status(thm)], ['7', '8'])).
% 2.09/2.26  thf('10', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 2.09/2.26      inference('demod', [status(thm)], ['6', '9'])).
% 2.09/2.26  thf(t10_xboole_1, axiom,
% 2.09/2.26    (![A:$i,B:$i,C:$i]:
% 2.09/2.26     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 2.09/2.26  thf('11', plain,
% 2.09/2.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.09/2.26         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 2.09/2.26      inference('cnf', [status(esa)], [t10_xboole_1])).
% 2.09/2.26  thf('12', plain,
% 2.09/2.26      (![X0 : $i]:
% 2.09/2.26         (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_B))),
% 2.09/2.26      inference('sup-', [status(thm)], ['10', '11'])).
% 2.09/2.26  thf(t8_xboole_1, axiom,
% 2.09/2.26    (![A:$i,B:$i,C:$i]:
% 2.09/2.26     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 2.09/2.26       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 2.09/2.26  thf('13', plain,
% 2.09/2.26      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.09/2.26         (~ (r1_tarski @ X10 @ X11)
% 2.09/2.26          | ~ (r1_tarski @ X12 @ X11)
% 2.09/2.26          | (r1_tarski @ (k2_xboole_0 @ X10 @ X12) @ X11))),
% 2.09/2.26      inference('cnf', [status(esa)], [t8_xboole_1])).
% 2.09/2.26  thf('14', plain,
% 2.09/2.26      (![X0 : $i, X1 : $i]:
% 2.09/2.26         ((r1_tarski @ (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ X1) @ 
% 2.09/2.26           (k2_xboole_0 @ X0 @ sk_B))
% 2.09/2.26          | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ sk_B)))),
% 2.09/2.26      inference('sup-', [status(thm)], ['12', '13'])).
% 2.09/2.26  thf('15', plain,
% 2.09/2.26      (![X0 : $i]:
% 2.09/2.26         (r1_tarski @ (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ X0) @ 
% 2.09/2.26          (k2_xboole_0 @ X0 @ sk_B))),
% 2.09/2.26      inference('sup-', [status(thm)], ['1', '14'])).
% 2.09/2.26  thf(d6_relat_1, axiom,
% 2.09/2.26    (![A:$i]:
% 2.09/2.26     ( ( v1_relat_1 @ A ) =>
% 2.09/2.26       ( ( k3_relat_1 @ A ) =
% 2.09/2.26         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 2.09/2.26  thf('16', plain,
% 2.09/2.26      (![X22 : $i]:
% 2.09/2.26         (((k3_relat_1 @ X22)
% 2.09/2.26            = (k2_xboole_0 @ (k1_relat_1 @ X22) @ (k2_relat_1 @ X22)))
% 2.09/2.26          | ~ (v1_relat_1 @ X22))),
% 2.09/2.26      inference('cnf', [status(esa)], [d6_relat_1])).
% 2.09/2.26  thf('17', plain,
% 2.09/2.26      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 2.09/2.26      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.09/2.26  thf('18', plain,
% 2.09/2.26      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.09/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.26  thf(cc2_relset_1, axiom,
% 2.09/2.26    (![A:$i,B:$i,C:$i]:
% 2.09/2.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.09/2.26       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.09/2.26  thf('19', plain,
% 2.09/2.26      (![X29 : $i, X30 : $i, X31 : $i]:
% 2.09/2.26         ((v4_relat_1 @ X29 @ X30)
% 2.09/2.26          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 2.09/2.26      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.09/2.26  thf('20', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 2.09/2.26      inference('sup-', [status(thm)], ['18', '19'])).
% 2.09/2.26  thf(t209_relat_1, axiom,
% 2.09/2.26    (![A:$i,B:$i]:
% 2.09/2.26     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 2.09/2.26       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 2.09/2.26  thf('21', plain,
% 2.09/2.26      (![X25 : $i, X26 : $i]:
% 2.09/2.26         (((X25) = (k7_relat_1 @ X25 @ X26))
% 2.09/2.26          | ~ (v4_relat_1 @ X25 @ X26)
% 2.09/2.26          | ~ (v1_relat_1 @ X25))),
% 2.09/2.26      inference('cnf', [status(esa)], [t209_relat_1])).
% 2.09/2.26  thf('22', plain,
% 2.09/2.26      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 2.09/2.26      inference('sup-', [status(thm)], ['20', '21'])).
% 2.09/2.26  thf('23', plain,
% 2.09/2.26      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.09/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.26  thf(cc2_relat_1, axiom,
% 2.09/2.26    (![A:$i]:
% 2.09/2.26     ( ( v1_relat_1 @ A ) =>
% 2.09/2.26       ( ![B:$i]:
% 2.09/2.26         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.09/2.26  thf('24', plain,
% 2.09/2.26      (![X20 : $i, X21 : $i]:
% 2.09/2.26         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 2.09/2.26          | (v1_relat_1 @ X20)
% 2.09/2.26          | ~ (v1_relat_1 @ X21))),
% 2.09/2.26      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.09/2.26  thf('25', plain,
% 2.09/2.26      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 2.09/2.26      inference('sup-', [status(thm)], ['23', '24'])).
% 2.09/2.26  thf(fc6_relat_1, axiom,
% 2.09/2.26    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.09/2.26  thf('26', plain,
% 2.09/2.26      (![X23 : $i, X24 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X23 @ X24))),
% 2.09/2.26      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.09/2.26  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 2.09/2.26      inference('demod', [status(thm)], ['25', '26'])).
% 2.09/2.26  thf('28', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 2.09/2.26      inference('demod', [status(thm)], ['22', '27'])).
% 2.09/2.26  thf(t87_relat_1, axiom,
% 2.09/2.26    (![A:$i,B:$i]:
% 2.09/2.26     ( ( v1_relat_1 @ B ) =>
% 2.09/2.26       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 2.09/2.26  thf('29', plain,
% 2.09/2.26      (![X27 : $i, X28 : $i]:
% 2.09/2.26         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X27 @ X28)) @ X28)
% 2.09/2.26          | ~ (v1_relat_1 @ X27))),
% 2.09/2.26      inference('cnf', [status(esa)], [t87_relat_1])).
% 2.09/2.26  thf('30', plain,
% 2.09/2.26      (((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A) | ~ (v1_relat_1 @ sk_C))),
% 2.09/2.26      inference('sup+', [status(thm)], ['28', '29'])).
% 2.09/2.26  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 2.09/2.26      inference('demod', [status(thm)], ['25', '26'])).
% 2.09/2.26  thf('32', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 2.09/2.26      inference('demod', [status(thm)], ['30', '31'])).
% 2.09/2.26  thf('33', plain,
% 2.09/2.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.09/2.26         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 2.09/2.26      inference('cnf', [status(esa)], [t10_xboole_1])).
% 2.09/2.26  thf('34', plain,
% 2.09/2.26      (![X0 : $i]:
% 2.09/2.26         (r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_A))),
% 2.09/2.26      inference('sup-', [status(thm)], ['32', '33'])).
% 2.09/2.26  thf('35', plain,
% 2.09/2.26      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.09/2.26         (~ (r1_tarski @ X10 @ X11)
% 2.09/2.26          | ~ (r1_tarski @ X12 @ X11)
% 2.09/2.26          | (r1_tarski @ (k2_xboole_0 @ X10 @ X12) @ X11))),
% 2.09/2.26      inference('cnf', [status(esa)], [t8_xboole_1])).
% 2.09/2.26  thf('36', plain,
% 2.09/2.26      (![X0 : $i, X1 : $i]:
% 2.09/2.26         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ X1) @ 
% 2.09/2.26           (k2_xboole_0 @ X0 @ sk_A))
% 2.09/2.26          | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ sk_A)))),
% 2.09/2.26      inference('sup-', [status(thm)], ['34', '35'])).
% 2.09/2.26  thf('37', plain,
% 2.09/2.26      (![X0 : $i]:
% 2.09/2.26         (r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ X0) @ 
% 2.09/2.26          (k2_xboole_0 @ X0 @ sk_A))),
% 2.09/2.26      inference('sup-', [status(thm)], ['17', '36'])).
% 2.09/2.26  thf('38', plain,
% 2.09/2.26      (((r1_tarski @ (k3_relat_1 @ sk_C) @ 
% 2.09/2.26         (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_A))
% 2.09/2.26        | ~ (v1_relat_1 @ sk_C))),
% 2.09/2.26      inference('sup+', [status(thm)], ['16', '37'])).
% 2.09/2.26  thf('39', plain, ((v1_relat_1 @ sk_C)),
% 2.09/2.26      inference('demod', [status(thm)], ['25', '26'])).
% 2.09/2.26  thf('40', plain,
% 2.09/2.26      ((r1_tarski @ (k3_relat_1 @ sk_C) @ 
% 2.09/2.26        (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_A))),
% 2.09/2.26      inference('demod', [status(thm)], ['38', '39'])).
% 2.09/2.26  thf(t12_xboole_1, axiom,
% 2.09/2.26    (![A:$i,B:$i]:
% 2.09/2.26     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 2.09/2.26  thf('41', plain,
% 2.09/2.26      (![X6 : $i, X7 : $i]:
% 2.09/2.26         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 2.09/2.26      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.09/2.26  thf('42', plain,
% 2.09/2.26      (((k2_xboole_0 @ (k3_relat_1 @ sk_C) @ 
% 2.09/2.26         (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_A))
% 2.09/2.26         = (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_A))),
% 2.09/2.26      inference('sup-', [status(thm)], ['40', '41'])).
% 2.09/2.26  thf(t11_xboole_1, axiom,
% 2.09/2.26    (![A:$i,B:$i,C:$i]:
% 2.09/2.26     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 2.09/2.26  thf('43', plain,
% 2.09/2.26      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.09/2.26         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 2.09/2.26      inference('cnf', [status(esa)], [t11_xboole_1])).
% 2.09/2.26  thf('44', plain,
% 2.09/2.26      (![X0 : $i]:
% 2.09/2.26         (~ (r1_tarski @ (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_A) @ X0)
% 2.09/2.26          | (r1_tarski @ (k3_relat_1 @ sk_C) @ X0))),
% 2.09/2.26      inference('sup-', [status(thm)], ['42', '43'])).
% 2.09/2.26  thf('45', plain,
% 2.09/2.26      ((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 2.09/2.26      inference('sup-', [status(thm)], ['15', '44'])).
% 2.09/2.26  thf('46', plain, ($false), inference('demod', [status(thm)], ['0', '45'])).
% 2.09/2.26  
% 2.09/2.26  % SZS output end Refutation
% 2.09/2.26  
% 2.09/2.27  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
