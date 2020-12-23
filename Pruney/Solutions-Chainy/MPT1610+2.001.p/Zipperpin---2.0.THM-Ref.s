%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QMNZEo1ICQ

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:13 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   63 (  75 expanded)
%              Number of leaves         :   26 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  331 ( 408 expanded)
%              Number of equality atoms :   39 (  48 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t18_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t18_yellow_1])).

thf('0',plain,(
    ( k3_yellow_0 @ ( k3_yellow_1 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( X9 != X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X10: $i] :
      ( r1_tarski @ X10 @ X10 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X15 )
      | ( X15
       != ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X24: $i] :
      ( ( k9_setfam_1 @ X24 )
      = ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ ( k9_setfam_1 @ X14 ) )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf(t83_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_zfmisc_1 @ ( k3_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ ( k1_zfmisc_1 @ X22 ) @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t83_zfmisc_1])).

thf('12',plain,(
    ! [X24: $i] :
      ( ( k9_setfam_1 @ X24 )
      = ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('13',plain,(
    ! [X24: $i] :
      ( ( k9_setfam_1 @ X24 )
      = ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('14',plain,(
    ! [X24: $i] :
      ( ( k9_setfam_1 @ X24 )
      = ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('15',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k9_setfam_1 @ ( k3_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ ( k9_setfam_1 @ X22 ) @ ( k9_setfam_1 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('17',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k9_setfam_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ X2 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','19'])).

thf(t13_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ k1_xboole_0 @ A )
       => ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) )
          = k1_xboole_0 ) ) ) )).

thf('21',plain,(
    ! [X25: $i] :
      ( ~ ( r2_hidden @ k1_xboole_0 @ X25 )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ X25 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t4_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k3_yellow_0 @ ( k3_yellow_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('25',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf(t46_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('27',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X19 ) @ X18 )
        = X18 )
      | ~ ( r2_hidden @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t46_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k9_setfam_1 @ X0 ) )
      = ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('29',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X20 ) @ X21 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k9_setfam_1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_setfam_1 @ X1 )
       != X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X1: $i] :
      ~ ( v1_xboole_0 @ ( k9_setfam_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_yellow_0 @ ( k3_yellow_1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['24','32'])).

thf('34',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','33'])).

thf('35',plain,(
    $false ),
    inference(simplify,[status(thm)],['34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QMNZEo1ICQ
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:19:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 156 iterations in 0.096s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.55  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.37/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.37/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.37/0.55  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.37/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.55  thf(t18_yellow_1, conjecture,
% 0.37/0.55    (![A:$i]: ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( k1_xboole_0 ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i]: ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t18_yellow_1])).
% 0.37/0.55  thf('0', plain, (((k3_yellow_0 @ (k3_yellow_1 @ sk_A)) != (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(commutativity_k3_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.37/0.55  thf('1', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.55  thf(t2_boole, axiom,
% 0.37/0.55    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.37/0.55  thf('2', plain,
% 0.37/0.55      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t2_boole])).
% 0.37/0.55  thf('3', plain,
% 0.37/0.55      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['1', '2'])).
% 0.37/0.55  thf(d10_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.55  thf('4', plain,
% 0.37/0.55      (![X9 : $i, X10 : $i]: ((r1_tarski @ X9 @ X10) | ((X9) != (X10)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.55  thf('5', plain, (![X10 : $i]: (r1_tarski @ X10 @ X10)),
% 0.37/0.55      inference('simplify', [status(thm)], ['4'])).
% 0.37/0.55  thf(d1_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.37/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.37/0.55  thf('6', plain,
% 0.37/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.55         (~ (r1_tarski @ X13 @ X14)
% 0.37/0.55          | (r2_hidden @ X13 @ X15)
% 0.37/0.55          | ((X15) != (k1_zfmisc_1 @ X14)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.37/0.55  thf('7', plain,
% 0.37/0.55      (![X13 : $i, X14 : $i]:
% 0.37/0.55         ((r2_hidden @ X13 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X13 @ X14))),
% 0.37/0.55      inference('simplify', [status(thm)], ['6'])).
% 0.37/0.55  thf(redefinition_k9_setfam_1, axiom,
% 0.37/0.55    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.37/0.55  thf('8', plain, (![X24 : $i]: ((k9_setfam_1 @ X24) = (k1_zfmisc_1 @ X24))),
% 0.37/0.55      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.37/0.55  thf('9', plain,
% 0.37/0.55      (![X13 : $i, X14 : $i]:
% 0.37/0.55         ((r2_hidden @ X13 @ (k9_setfam_1 @ X14)) | ~ (r1_tarski @ X13 @ X14))),
% 0.37/0.55      inference('demod', [status(thm)], ['7', '8'])).
% 0.37/0.55  thf('10', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k9_setfam_1 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['5', '9'])).
% 0.37/0.55  thf(t83_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( k1_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) ) =
% 0.37/0.55       ( k3_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.37/0.55  thf('11', plain,
% 0.37/0.55      (![X22 : $i, X23 : $i]:
% 0.37/0.55         ((k1_zfmisc_1 @ (k3_xboole_0 @ X22 @ X23))
% 0.37/0.55           = (k3_xboole_0 @ (k1_zfmisc_1 @ X22) @ (k1_zfmisc_1 @ X23)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t83_zfmisc_1])).
% 0.37/0.55  thf('12', plain, (![X24 : $i]: ((k9_setfam_1 @ X24) = (k1_zfmisc_1 @ X24))),
% 0.37/0.55      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.37/0.55  thf('13', plain, (![X24 : $i]: ((k9_setfam_1 @ X24) = (k1_zfmisc_1 @ X24))),
% 0.37/0.55      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.37/0.55  thf('14', plain, (![X24 : $i]: ((k9_setfam_1 @ X24) = (k1_zfmisc_1 @ X24))),
% 0.37/0.55      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.37/0.55  thf('15', plain,
% 0.37/0.55      (![X22 : $i, X23 : $i]:
% 0.37/0.55         ((k9_setfam_1 @ (k3_xboole_0 @ X22 @ X23))
% 0.37/0.55           = (k3_xboole_0 @ (k9_setfam_1 @ X22) @ (k9_setfam_1 @ X23)))),
% 0.37/0.55      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 0.37/0.55  thf(d4_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.37/0.55       ( ![D:$i]:
% 0.37/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.55           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.37/0.55  thf('16', plain,
% 0.37/0.55      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X6 @ X5)
% 0.37/0.55          | (r2_hidden @ X6 @ X4)
% 0.37/0.55          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.37/0.55  thf('17', plain,
% 0.37/0.55      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.37/0.55         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['16'])).
% 0.37/0.55  thf('18', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X2 @ (k9_setfam_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.37/0.55          | (r2_hidden @ X2 @ (k9_setfam_1 @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['15', '17'])).
% 0.37/0.55  thf('19', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (r2_hidden @ (k3_xboole_0 @ X1 @ X0) @ (k9_setfam_1 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['10', '18'])).
% 0.37/0.55  thf('20', plain,
% 0.37/0.55      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k9_setfam_1 @ X0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['3', '19'])).
% 0.37/0.55  thf(t13_yellow_1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.37/0.55       ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.37/0.55         ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ))).
% 0.37/0.55  thf('21', plain,
% 0.37/0.55      (![X25 : $i]:
% 0.37/0.55         (~ (r2_hidden @ k1_xboole_0 @ X25)
% 0.37/0.55          | ((k3_yellow_0 @ (k2_yellow_1 @ X25)) = (k1_xboole_0))
% 0.37/0.55          | (v1_xboole_0 @ X25))),
% 0.37/0.55      inference('cnf', [status(esa)], [t13_yellow_1])).
% 0.37/0.55  thf('22', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.37/0.55          | ((k3_yellow_0 @ (k2_yellow_1 @ (k9_setfam_1 @ X0))) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.55  thf(t4_yellow_1, axiom,
% 0.37/0.55    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ))).
% 0.37/0.55  thf('23', plain,
% 0.37/0.55      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k2_yellow_1 @ (k9_setfam_1 @ X26)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.37/0.55  thf('24', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.37/0.55          | ((k3_yellow_0 @ (k3_yellow_1 @ X0)) = (k1_xboole_0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['22', '23'])).
% 0.37/0.55  thf(l13_xboole_0, axiom,
% 0.37/0.55    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.55  thf('25', plain,
% 0.37/0.55      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X8))),
% 0.37/0.55      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.37/0.55  thf('26', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k9_setfam_1 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['5', '9'])).
% 0.37/0.55  thf(t46_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( r2_hidden @ A @ B ) =>
% 0.37/0.55       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.37/0.55  thf('27', plain,
% 0.37/0.55      (![X18 : $i, X19 : $i]:
% 0.37/0.55         (((k2_xboole_0 @ (k1_tarski @ X19) @ X18) = (X18))
% 0.37/0.55          | ~ (r2_hidden @ X19 @ X18))),
% 0.37/0.55      inference('cnf', [status(esa)], [t46_zfmisc_1])).
% 0.37/0.55  thf('28', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k9_setfam_1 @ X0))
% 0.37/0.55           = (k9_setfam_1 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.37/0.55  thf(t49_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.37/0.55  thf('29', plain,
% 0.37/0.55      (![X20 : $i, X21 : $i]:
% 0.37/0.55         ((k2_xboole_0 @ (k1_tarski @ X20) @ X21) != (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.37/0.55  thf('30', plain, (![X0 : $i]: ((k9_setfam_1 @ X0) != (k1_xboole_0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.37/0.55  thf('31', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (((k9_setfam_1 @ X1) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['25', '30'])).
% 0.37/0.55  thf('32', plain, (![X1 : $i]: ~ (v1_xboole_0 @ (k9_setfam_1 @ X1))),
% 0.37/0.55      inference('simplify', [status(thm)], ['31'])).
% 0.37/0.55  thf('33', plain,
% 0.37/0.55      (![X0 : $i]: ((k3_yellow_0 @ (k3_yellow_1 @ X0)) = (k1_xboole_0))),
% 0.37/0.55      inference('clc', [status(thm)], ['24', '32'])).
% 0.37/0.55  thf('34', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.37/0.55      inference('demod', [status(thm)], ['0', '33'])).
% 0.37/0.55  thf('35', plain, ($false), inference('simplify', [status(thm)], ['34'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
