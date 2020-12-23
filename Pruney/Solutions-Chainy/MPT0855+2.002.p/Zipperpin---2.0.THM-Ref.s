%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SyVx2WceRR

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 (  55 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  273 ( 465 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t11_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) )
     => ( ! [D: $i,E: $i] :
            ( A
           != ( k4_tarski @ D @ E ) )
        | ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
          & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) )
       => ( ! [D: $i,E: $i] :
              ( A
             != ( k4_tarski @ D @ E ) )
          | ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t11_mcart_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( sk_A
    = ( k4_tarski @ sk_D_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('4',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_D_1 ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    r2_hidden @ sk_D_1 @ sk_B ),
    inference(demod,[status(thm)],['1','4'])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ X6 )
        = X6 )
      | ~ ( r2_hidden @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('7',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X8 @ X9 ) @ ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('9',plain,
    ( sk_A
    = ( k4_tarski @ sk_D_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( sk_A
    = ( k4_tarski @ sk_D_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X17: $i,X19: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X17 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('13',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_E ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    r2_hidden @ sk_E @ sk_C ),
    inference(demod,[status(thm)],['10','13'])).

thf(t128_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
    <=> ( ( A = C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X12 ) @ X16 ) )
      | ~ ( r2_hidden @ X14 @ X16 )
      | ( X13 != X12 ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('16',plain,(
    ! [X12: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X12 ) @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ sk_E ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_D_1 ) @ sk_C ) ),
    inference('sup+',[status(thm)],['9','17'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_D_1 ) @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ X0 ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['8','21'])).

thf('23',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['7','22'])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['0','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SyVx2WceRR
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:26:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 142 iterations in 0.108s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.56  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.56  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.56  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.56  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.56  thf(t11_mcart_1, conjecture,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.56         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) =>
% 0.20/0.56       ( ( ![D:$i,E:$i]: ( ( A ) != ( k4_tarski @ D @ E ) ) ) | 
% 0.20/0.56         ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.56        ( ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.56            ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) =>
% 0.20/0.56          ( ( ![D:$i,E:$i]: ( ( A ) != ( k4_tarski @ D @ E ) ) ) | 
% 0.20/0.56            ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t11_mcart_1])).
% 0.20/0.56  thf('0', plain, (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('1', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('2', plain, (((sk_A) = (k4_tarski @ sk_D_1 @ sk_E))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(t7_mcart_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.56       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.56  thf('3', plain,
% 0.20/0.56      (![X17 : $i, X18 : $i]: ((k1_mcart_1 @ (k4_tarski @ X17 @ X18)) = (X17))),
% 0.20/0.56      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.56  thf('4', plain, (((k1_mcart_1 @ sk_A) = (sk_D_1))),
% 0.20/0.56      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.56  thf('5', plain, ((r2_hidden @ sk_D_1 @ sk_B)),
% 0.20/0.56      inference('demod', [status(thm)], ['1', '4'])).
% 0.20/0.56  thf(l22_zfmisc_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( r2_hidden @ A @ B ) =>
% 0.20/0.56       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      (![X6 : $i, X7 : $i]:
% 0.20/0.56         (((k2_xboole_0 @ (k1_tarski @ X7) @ X6) = (X6))
% 0.20/0.56          | ~ (r2_hidden @ X7 @ X6))),
% 0.20/0.56      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.20/0.56  thf('7', plain, (((k2_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_B) = (sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.56  thf(t120_zfmisc_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.20/0.56         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.20/0.56       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.56         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.20/0.56  thf('8', plain,
% 0.20/0.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.56         ((k2_zfmisc_1 @ (k2_xboole_0 @ X8 @ X10) @ X9)
% 0.20/0.56           = (k2_xboole_0 @ (k2_zfmisc_1 @ X8 @ X9) @ (k2_zfmisc_1 @ X10 @ X9)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 0.20/0.56  thf('9', plain, (((sk_A) = (k4_tarski @ sk_D_1 @ sk_E))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('10', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('11', plain, (((sk_A) = (k4_tarski @ sk_D_1 @ sk_E))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('12', plain,
% 0.20/0.56      (![X17 : $i, X19 : $i]: ((k2_mcart_1 @ (k4_tarski @ X17 @ X19)) = (X19))),
% 0.20/0.56      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.56  thf('13', plain, (((k2_mcart_1 @ sk_A) = (sk_E))),
% 0.20/0.56      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.56  thf('14', plain, ((r2_hidden @ sk_E @ sk_C)),
% 0.20/0.56      inference('demod', [status(thm)], ['10', '13'])).
% 0.20/0.56  thf(t128_zfmisc_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.56     ( ( r2_hidden @
% 0.20/0.56         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.20/0.56       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.20/0.56  thf('15', plain,
% 0.20/0.56      (![X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 0.20/0.56         ((r2_hidden @ (k4_tarski @ X13 @ X14) @ 
% 0.20/0.56           (k2_zfmisc_1 @ (k1_tarski @ X12) @ X16))
% 0.20/0.56          | ~ (r2_hidden @ X14 @ X16)
% 0.20/0.56          | ((X13) != (X12)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 0.20/0.56  thf('16', plain,
% 0.20/0.56      (![X12 : $i, X14 : $i, X16 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X14 @ X16)
% 0.20/0.56          | (r2_hidden @ (k4_tarski @ X12 @ X14) @ 
% 0.20/0.56             (k2_zfmisc_1 @ (k1_tarski @ X12) @ X16)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.56  thf('17', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (r2_hidden @ (k4_tarski @ X0 @ sk_E) @ 
% 0.20/0.56          (k2_zfmisc_1 @ (k1_tarski @ X0) @ sk_C))),
% 0.20/0.56      inference('sup-', [status(thm)], ['14', '16'])).
% 0.20/0.56  thf('18', plain,
% 0.20/0.56      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k1_tarski @ sk_D_1) @ sk_C))),
% 0.20/0.56      inference('sup+', [status(thm)], ['9', '17'])).
% 0.20/0.56  thf(d3_xboole_0, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.20/0.56       ( ![D:$i]:
% 0.20/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.56           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.56  thf('19', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X0 @ X3)
% 0.20/0.56          | (r2_hidden @ X0 @ X2)
% 0.20/0.56          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.20/0.56      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.20/0.56  thf('20', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.20/0.56         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 0.20/0.56      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.56  thf('21', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (r2_hidden @ sk_A @ 
% 0.20/0.56          (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_D_1) @ sk_C) @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['18', '20'])).
% 0.20/0.56  thf('22', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (r2_hidden @ sk_A @ 
% 0.20/0.56          (k2_zfmisc_1 @ (k2_xboole_0 @ (k1_tarski @ sk_D_1) @ X0) @ sk_C))),
% 0.20/0.56      inference('sup+', [status(thm)], ['8', '21'])).
% 0.20/0.56  thf('23', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.56      inference('sup+', [status(thm)], ['7', '22'])).
% 0.20/0.56  thf('24', plain, ($false), inference('demod', [status(thm)], ['0', '23'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.20/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
