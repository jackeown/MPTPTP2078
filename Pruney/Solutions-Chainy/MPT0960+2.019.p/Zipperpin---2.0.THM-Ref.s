%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cXhhmKLjG9

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:36 EST 2020

% Result     : Theorem 5.19s
% Output     : Refutation 5.19s
% Verified   : 
% Statistics : Number of formulae       :   72 (  90 expanded)
%              Number of leaves         :   22 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :  498 ( 642 expanded)
%              Number of equality atoms :   21 (  32 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t33_wellord2,conjecture,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t33_wellord2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_wellord2 @ sk_A ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k1_wellord2 @ A ) )
      <=> ( ( ( k3_relat_1 @ B )
            = A )
          & ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A ) )
             => ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r1_tarski @ C @ D ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X19
       != ( k1_wellord2 @ X18 ) )
      | ( ( k3_relat_1 @ X19 )
        = X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('2',plain,(
    ! [X18: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X18 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X18 ) )
        = X18 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('3',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('4',plain,(
    ! [X18: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X18 ) )
      = X18 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X16: $i] :
      ( ( ( k3_relat_1 @ X16 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X16 ) @ ( k2_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','10'])).

thf('12',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X15 @ X13 ) @ ( k2_zfmisc_1 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('17',plain,(
    ! [X18: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X18 ) )
      = X18 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('18',plain,(
    ! [X16: $i] :
      ( ( ( k3_relat_1 @ X16 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X16 ) @ ( k2_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('25',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('28',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X13 @ X15 ) @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ X2 ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k2_zfmisc_1 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('32',plain,(
    ! [X17: $i] :
      ( ( r1_tarski @ X17 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X17 ) @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('33',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_xboole_0 @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('36',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) @ X3 )
      | ( r1_tarski @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) @ X2 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ X0 ) ) @ X2 )
      | ( r1_tarski @ X0 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','43'])).

thf('45',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) @ X1 )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['0','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cXhhmKLjG9
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:29:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 5.19/5.41  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.19/5.41  % Solved by: fo/fo7.sh
% 5.19/5.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.19/5.41  % done 3891 iterations in 4.930s
% 5.19/5.41  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.19/5.41  % SZS output start Refutation
% 5.19/5.41  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 5.19/5.41  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.19/5.41  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 5.19/5.41  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.19/5.41  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.19/5.41  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.19/5.41  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.19/5.41  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.19/5.41  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 5.19/5.41  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.19/5.41  thf(sk_A_type, type, sk_A: $i).
% 5.19/5.41  thf(t33_wellord2, conjecture,
% 5.19/5.41    (![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ))).
% 5.19/5.41  thf(zf_stmt_0, negated_conjecture,
% 5.19/5.41    (~( ![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )),
% 5.19/5.41    inference('cnf.neg', [status(esa)], [t33_wellord2])).
% 5.19/5.41  thf('0', plain,
% 5.19/5.41      (~ (r1_tarski @ (k1_wellord2 @ sk_A) @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 5.19/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.19/5.41  thf(d1_wellord2, axiom,
% 5.19/5.41    (![A:$i,B:$i]:
% 5.19/5.41     ( ( v1_relat_1 @ B ) =>
% 5.19/5.41       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 5.19/5.41         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 5.19/5.41           ( ![C:$i,D:$i]:
% 5.19/5.41             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 5.19/5.41               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 5.19/5.41                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 5.19/5.41  thf('1', plain,
% 5.19/5.41      (![X18 : $i, X19 : $i]:
% 5.19/5.41         (((X19) != (k1_wellord2 @ X18))
% 5.19/5.41          | ((k3_relat_1 @ X19) = (X18))
% 5.19/5.41          | ~ (v1_relat_1 @ X19))),
% 5.19/5.41      inference('cnf', [status(esa)], [d1_wellord2])).
% 5.19/5.41  thf('2', plain,
% 5.19/5.41      (![X18 : $i]:
% 5.19/5.41         (~ (v1_relat_1 @ (k1_wellord2 @ X18))
% 5.19/5.41          | ((k3_relat_1 @ (k1_wellord2 @ X18)) = (X18)))),
% 5.19/5.41      inference('simplify', [status(thm)], ['1'])).
% 5.19/5.41  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 5.19/5.41  thf('3', plain, (![X22 : $i]: (v1_relat_1 @ (k1_wellord2 @ X22))),
% 5.19/5.41      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 5.19/5.41  thf('4', plain, (![X18 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X18)) = (X18))),
% 5.19/5.41      inference('demod', [status(thm)], ['2', '3'])).
% 5.19/5.41  thf(d6_relat_1, axiom,
% 5.19/5.41    (![A:$i]:
% 5.19/5.41     ( ( v1_relat_1 @ A ) =>
% 5.19/5.41       ( ( k3_relat_1 @ A ) =
% 5.19/5.41         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 5.19/5.41  thf('5', plain,
% 5.19/5.41      (![X16 : $i]:
% 5.19/5.41         (((k3_relat_1 @ X16)
% 5.19/5.41            = (k2_xboole_0 @ (k1_relat_1 @ X16) @ (k2_relat_1 @ X16)))
% 5.19/5.41          | ~ (v1_relat_1 @ X16))),
% 5.19/5.41      inference('cnf', [status(esa)], [d6_relat_1])).
% 5.19/5.41  thf(d10_xboole_0, axiom,
% 5.19/5.41    (![A:$i,B:$i]:
% 5.19/5.41     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.19/5.41  thf('6', plain,
% 5.19/5.41      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 5.19/5.41      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.19/5.41  thf('7', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 5.19/5.41      inference('simplify', [status(thm)], ['6'])).
% 5.19/5.41  thf(t10_xboole_1, axiom,
% 5.19/5.41    (![A:$i,B:$i,C:$i]:
% 5.19/5.41     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 5.19/5.41  thf('8', plain,
% 5.19/5.41      (![X3 : $i, X4 : $i, X5 : $i]:
% 5.19/5.41         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 5.19/5.41      inference('cnf', [status(esa)], [t10_xboole_1])).
% 5.19/5.41  thf('9', plain,
% 5.19/5.41      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 5.19/5.41      inference('sup-', [status(thm)], ['7', '8'])).
% 5.19/5.41  thf('10', plain,
% 5.19/5.41      (![X0 : $i]:
% 5.19/5.41         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 5.19/5.41          | ~ (v1_relat_1 @ X0))),
% 5.19/5.41      inference('sup+', [status(thm)], ['5', '9'])).
% 5.19/5.41  thf('11', plain,
% 5.19/5.41      (![X0 : $i]:
% 5.19/5.41         ((r1_tarski @ (k2_relat_1 @ (k1_wellord2 @ X0)) @ X0)
% 5.19/5.41          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 5.19/5.41      inference('sup+', [status(thm)], ['4', '10'])).
% 5.19/5.41  thf('12', plain, (![X22 : $i]: (v1_relat_1 @ (k1_wellord2 @ X22))),
% 5.19/5.41      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 5.19/5.41  thf('13', plain,
% 5.19/5.41      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k1_wellord2 @ X0)) @ X0)),
% 5.19/5.41      inference('demod', [status(thm)], ['11', '12'])).
% 5.19/5.41  thf(t118_zfmisc_1, axiom,
% 5.19/5.41    (![A:$i,B:$i,C:$i]:
% 5.19/5.41     ( ( r1_tarski @ A @ B ) =>
% 5.19/5.41       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 5.19/5.41         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 5.19/5.41  thf('14', plain,
% 5.19/5.41      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.19/5.41         (~ (r1_tarski @ X13 @ X14)
% 5.19/5.41          | (r1_tarski @ (k2_zfmisc_1 @ X15 @ X13) @ (k2_zfmisc_1 @ X15 @ X14)))),
% 5.19/5.41      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 5.19/5.41  thf('15', plain,
% 5.19/5.41      (![X0 : $i, X1 : $i]:
% 5.19/5.41         (r1_tarski @ (k2_zfmisc_1 @ X1 @ (k2_relat_1 @ (k1_wellord2 @ X0))) @ 
% 5.19/5.41          (k2_zfmisc_1 @ X1 @ X0))),
% 5.19/5.41      inference('sup-', [status(thm)], ['13', '14'])).
% 5.19/5.41  thf('16', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 5.19/5.41      inference('simplify', [status(thm)], ['6'])).
% 5.19/5.41  thf('17', plain, (![X18 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X18)) = (X18))),
% 5.19/5.41      inference('demod', [status(thm)], ['2', '3'])).
% 5.19/5.41  thf('18', plain,
% 5.19/5.41      (![X16 : $i]:
% 5.19/5.41         (((k3_relat_1 @ X16)
% 5.19/5.41            = (k2_xboole_0 @ (k1_relat_1 @ X16) @ (k2_relat_1 @ X16)))
% 5.19/5.41          | ~ (v1_relat_1 @ X16))),
% 5.19/5.41      inference('cnf', [status(esa)], [d6_relat_1])).
% 5.19/5.41  thf(t11_xboole_1, axiom,
% 5.19/5.41    (![A:$i,B:$i,C:$i]:
% 5.19/5.41     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 5.19/5.41  thf('19', plain,
% 5.19/5.41      (![X6 : $i, X7 : $i, X8 : $i]:
% 5.19/5.41         ((r1_tarski @ X6 @ X7) | ~ (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ X7))),
% 5.19/5.41      inference('cnf', [status(esa)], [t11_xboole_1])).
% 5.19/5.41  thf('20', plain,
% 5.19/5.41      (![X0 : $i, X1 : $i]:
% 5.19/5.41         (~ (r1_tarski @ (k3_relat_1 @ X0) @ X1)
% 5.19/5.41          | ~ (v1_relat_1 @ X0)
% 5.19/5.41          | (r1_tarski @ (k1_relat_1 @ X0) @ X1))),
% 5.19/5.41      inference('sup-', [status(thm)], ['18', '19'])).
% 5.19/5.41  thf('21', plain,
% 5.19/5.41      (![X0 : $i, X1 : $i]:
% 5.19/5.41         (~ (r1_tarski @ X0 @ X1)
% 5.19/5.41          | (r1_tarski @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X1)
% 5.19/5.41          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 5.19/5.41      inference('sup-', [status(thm)], ['17', '20'])).
% 5.19/5.41  thf('22', plain, (![X22 : $i]: (v1_relat_1 @ (k1_wellord2 @ X22))),
% 5.19/5.41      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 5.19/5.41  thf('23', plain,
% 5.19/5.41      (![X0 : $i, X1 : $i]:
% 5.19/5.41         (~ (r1_tarski @ X0 @ X1)
% 5.19/5.41          | (r1_tarski @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X1))),
% 5.19/5.41      inference('demod', [status(thm)], ['21', '22'])).
% 5.19/5.41  thf('24', plain,
% 5.19/5.41      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X0)),
% 5.19/5.41      inference('sup-', [status(thm)], ['16', '23'])).
% 5.19/5.41  thf(t12_xboole_1, axiom,
% 5.19/5.41    (![A:$i,B:$i]:
% 5.19/5.41     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 5.19/5.41  thf('25', plain,
% 5.19/5.41      (![X9 : $i, X10 : $i]:
% 5.19/5.41         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 5.19/5.41      inference('cnf', [status(esa)], [t12_xboole_1])).
% 5.19/5.41  thf('26', plain,
% 5.19/5.41      (![X0 : $i]:
% 5.19/5.41         ((k2_xboole_0 @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X0) = (X0))),
% 5.19/5.41      inference('sup-', [status(thm)], ['24', '25'])).
% 5.19/5.41  thf(t7_xboole_1, axiom,
% 5.19/5.41    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 5.19/5.41  thf('27', plain,
% 5.19/5.41      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 5.19/5.41      inference('cnf', [status(esa)], [t7_xboole_1])).
% 5.19/5.41  thf('28', plain,
% 5.19/5.41      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.19/5.41         (~ (r1_tarski @ X13 @ X14)
% 5.19/5.41          | (r1_tarski @ (k2_zfmisc_1 @ X13 @ X15) @ (k2_zfmisc_1 @ X14 @ X15)))),
% 5.19/5.41      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 5.19/5.41  thf('29', plain,
% 5.19/5.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.19/5.41         (r1_tarski @ (k2_zfmisc_1 @ X1 @ X2) @ 
% 5.19/5.41          (k2_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 5.19/5.41      inference('sup-', [status(thm)], ['27', '28'])).
% 5.19/5.41  thf('30', plain,
% 5.19/5.41      (![X9 : $i, X10 : $i]:
% 5.19/5.41         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 5.19/5.41      inference('cnf', [status(esa)], [t12_xboole_1])).
% 5.19/5.41  thf('31', plain,
% 5.19/5.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.19/5.41         ((k2_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ 
% 5.19/5.41           (k2_zfmisc_1 @ (k2_xboole_0 @ X2 @ X1) @ X0))
% 5.19/5.41           = (k2_zfmisc_1 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 5.19/5.41      inference('sup-', [status(thm)], ['29', '30'])).
% 5.19/5.41  thf(t21_relat_1, axiom,
% 5.19/5.41    (![A:$i]:
% 5.19/5.41     ( ( v1_relat_1 @ A ) =>
% 5.19/5.41       ( r1_tarski @
% 5.19/5.41         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 5.19/5.41  thf('32', plain,
% 5.19/5.41      (![X17 : $i]:
% 5.19/5.41         ((r1_tarski @ X17 @ 
% 5.19/5.41           (k2_zfmisc_1 @ (k1_relat_1 @ X17) @ (k2_relat_1 @ X17)))
% 5.19/5.41          | ~ (v1_relat_1 @ X17))),
% 5.19/5.41      inference('cnf', [status(esa)], [t21_relat_1])).
% 5.19/5.41  thf('33', plain,
% 5.19/5.41      (![X9 : $i, X10 : $i]:
% 5.19/5.41         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 5.19/5.41      inference('cnf', [status(esa)], [t12_xboole_1])).
% 5.19/5.41  thf('34', plain,
% 5.19/5.41      (![X0 : $i]:
% 5.19/5.41         (~ (v1_relat_1 @ X0)
% 5.19/5.41          | ((k2_xboole_0 @ X0 @ 
% 5.19/5.41              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 5.19/5.41              = (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 5.19/5.41      inference('sup-', [status(thm)], ['32', '33'])).
% 5.19/5.41  thf('35', plain,
% 5.19/5.41      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 5.19/5.41      inference('cnf', [status(esa)], [t7_xboole_1])).
% 5.19/5.41  thf('36', plain,
% 5.19/5.41      (![X6 : $i, X7 : $i, X8 : $i]:
% 5.19/5.41         ((r1_tarski @ X6 @ X7) | ~ (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ X7))),
% 5.19/5.41      inference('cnf', [status(esa)], [t11_xboole_1])).
% 5.19/5.41  thf('37', plain,
% 5.19/5.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.19/5.41         (r1_tarski @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 5.19/5.41      inference('sup-', [status(thm)], ['35', '36'])).
% 5.19/5.41  thf('38', plain,
% 5.19/5.41      (![X9 : $i, X10 : $i]:
% 5.19/5.41         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 5.19/5.41      inference('cnf', [status(esa)], [t12_xboole_1])).
% 5.19/5.41  thf('39', plain,
% 5.19/5.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.19/5.41         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))
% 5.19/5.41           = (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 5.19/5.41      inference('sup-', [status(thm)], ['37', '38'])).
% 5.19/5.41  thf('40', plain,
% 5.19/5.41      (![X6 : $i, X7 : $i, X8 : $i]:
% 5.19/5.41         ((r1_tarski @ X6 @ X7) | ~ (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ X7))),
% 5.19/5.41      inference('cnf', [status(esa)], [t11_xboole_1])).
% 5.19/5.41  thf('41', plain,
% 5.19/5.41      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.19/5.41         (~ (r1_tarski @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0) @ X3)
% 5.19/5.41          | (r1_tarski @ X2 @ X3))),
% 5.19/5.41      inference('sup-', [status(thm)], ['39', '40'])).
% 5.19/5.41  thf('42', plain,
% 5.19/5.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.19/5.41         (~ (r1_tarski @ 
% 5.19/5.41             (k2_xboole_0 @ 
% 5.19/5.41              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ X2) @ 
% 5.19/5.41             X1)
% 5.19/5.41          | ~ (v1_relat_1 @ X0)
% 5.19/5.41          | (r1_tarski @ X0 @ X1))),
% 5.19/5.41      inference('sup-', [status(thm)], ['34', '41'])).
% 5.19/5.41  thf('43', plain,
% 5.19/5.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.19/5.41         (~ (r1_tarski @ 
% 5.19/5.41             (k2_zfmisc_1 @ (k2_xboole_0 @ (k1_relat_1 @ X0) @ X1) @ 
% 5.19/5.41              (k2_relat_1 @ X0)) @ 
% 5.19/5.41             X2)
% 5.19/5.41          | (r1_tarski @ X0 @ X2)
% 5.19/5.41          | ~ (v1_relat_1 @ X0))),
% 5.19/5.41      inference('sup-', [status(thm)], ['31', '42'])).
% 5.19/5.41  thf('44', plain,
% 5.19/5.41      (![X0 : $i, X1 : $i]:
% 5.19/5.41         (~ (r1_tarski @ 
% 5.19/5.41             (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0))) @ X1)
% 5.19/5.41          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 5.19/5.41          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 5.19/5.41      inference('sup-', [status(thm)], ['26', '43'])).
% 5.19/5.41  thf('45', plain, (![X22 : $i]: (v1_relat_1 @ (k1_wellord2 @ X22))),
% 5.19/5.41      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 5.19/5.41  thf('46', plain,
% 5.19/5.41      (![X0 : $i, X1 : $i]:
% 5.19/5.41         (~ (r1_tarski @ 
% 5.19/5.41             (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0))) @ X1)
% 5.19/5.41          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 5.19/5.41      inference('demod', [status(thm)], ['44', '45'])).
% 5.19/5.41  thf('47', plain,
% 5.19/5.41      (![X0 : $i]: (r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))),
% 5.19/5.41      inference('sup-', [status(thm)], ['15', '46'])).
% 5.19/5.41  thf('48', plain, ($false), inference('demod', [status(thm)], ['0', '47'])).
% 5.19/5.41  
% 5.19/5.41  % SZS output end Refutation
% 5.19/5.41  
% 5.27/5.41  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
