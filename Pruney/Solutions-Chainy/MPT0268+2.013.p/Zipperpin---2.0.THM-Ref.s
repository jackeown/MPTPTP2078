%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.p436AFIL6P

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:53 EST 2020

% Result     : Theorem 0.65s
% Output     : Refutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 117 expanded)
%              Number of leaves         :   15 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :  469 ( 966 expanded)
%              Number of equality atoms :   49 ( 100 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(t65_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = A )
      <=> ~ ( r2_hidden @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t65_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('5',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( X32 != X31 )
      | ( r2_hidden @ X32 @ X33 )
      | ( X33
       != ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('6',plain,(
    ! [X31: $i] :
      ( r2_hidden @ X31 @ ( k1_tarski @ X31 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('9',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','12'])).

thf('14',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('16',plain,(
    ! [X31: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X34 @ X33 )
      | ( X34 = X31 )
      | ( X33
       != ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('17',plain,(
    ! [X31: $i,X34: $i] :
      ( ( X34 = X31 )
      | ~ ( r2_hidden @ X34 @ ( k1_tarski @ X31 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( k1_tarski @ X0 ) @ X1 ) @ X2 )
      | ( X2
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_D @ X2 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('19',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('20',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ k1_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = X1 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['21'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['21'])).

thf('34',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['30','38'])).

thf('40',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('41',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('42',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['2','12','41'])).

thf('43',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['40','42'])).

thf('44',plain,
    ( ( sk_A != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf('45',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['14','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.p436AFIL6P
% 0.15/0.37  % Computer   : n010.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 10:39:45 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.23/0.38  % Running in FO mode
% 0.65/0.86  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.65/0.86  % Solved by: fo/fo7.sh
% 0.65/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.65/0.86  % done 684 iterations in 0.380s
% 0.65/0.86  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.65/0.86  % SZS output start Refutation
% 0.65/0.86  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.65/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.65/0.86  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.65/0.86  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.65/0.86  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.65/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.65/0.86  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.65/0.86  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.65/0.86  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.65/0.86  thf(t65_zfmisc_1, conjecture,
% 0.65/0.86    (![A:$i,B:$i]:
% 0.65/0.86     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.65/0.86       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.65/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.65/0.86    (~( ![A:$i,B:$i]:
% 0.65/0.86        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.65/0.86          ( ~( r2_hidden @ B @ A ) ) ) )),
% 0.65/0.86    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 0.65/0.86  thf('0', plain,
% 0.65/0.86      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.65/0.86        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('1', plain,
% 0.65/0.86      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 0.65/0.86      inference('split', [status(esa)], ['0'])).
% 0.65/0.86  thf('2', plain,
% 0.65/0.86      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 0.65/0.86       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.65/0.86      inference('split', [status(esa)], ['0'])).
% 0.65/0.86  thf('3', plain,
% 0.65/0.86      (((r2_hidden @ sk_B @ sk_A)
% 0.65/0.86        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('4', plain,
% 0.65/0.86      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.65/0.86      inference('split', [status(esa)], ['3'])).
% 0.65/0.86  thf(d1_tarski, axiom,
% 0.65/0.86    (![A:$i,B:$i]:
% 0.65/0.86     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.65/0.86       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.65/0.86  thf('5', plain,
% 0.65/0.86      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.65/0.86         (((X32) != (X31))
% 0.65/0.86          | (r2_hidden @ X32 @ X33)
% 0.65/0.86          | ((X33) != (k1_tarski @ X31)))),
% 0.65/0.86      inference('cnf', [status(esa)], [d1_tarski])).
% 0.65/0.86  thf('6', plain, (![X31 : $i]: (r2_hidden @ X31 @ (k1_tarski @ X31))),
% 0.65/0.86      inference('simplify', [status(thm)], ['5'])).
% 0.65/0.86  thf('7', plain,
% 0.65/0.86      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 0.65/0.86         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.65/0.86      inference('split', [status(esa)], ['0'])).
% 0.65/0.86  thf(d5_xboole_0, axiom,
% 0.65/0.86    (![A:$i,B:$i,C:$i]:
% 0.65/0.86     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.65/0.86       ( ![D:$i]:
% 0.65/0.86         ( ( r2_hidden @ D @ C ) <=>
% 0.65/0.86           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.65/0.86  thf('8', plain,
% 0.65/0.86      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.65/0.86         (~ (r2_hidden @ X12 @ X11)
% 0.65/0.86          | ~ (r2_hidden @ X12 @ X10)
% 0.65/0.86          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 0.65/0.86      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.65/0.86  thf('9', plain,
% 0.65/0.86      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.65/0.86         (~ (r2_hidden @ X12 @ X10)
% 0.65/0.86          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.65/0.86      inference('simplify', [status(thm)], ['8'])).
% 0.65/0.86  thf('10', plain,
% 0.65/0.86      ((![X0 : $i]:
% 0.65/0.86          (~ (r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))))
% 0.65/0.86         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['7', '9'])).
% 0.65/0.86  thf('11', plain,
% 0.65/0.86      ((~ (r2_hidden @ sk_B @ sk_A))
% 0.65/0.86         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['6', '10'])).
% 0.65/0.86  thf('12', plain,
% 0.65/0.86      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 0.65/0.86       ~ ((r2_hidden @ sk_B @ sk_A))),
% 0.65/0.86      inference('sup-', [status(thm)], ['4', '11'])).
% 0.65/0.86  thf('13', plain, (~ ((r2_hidden @ sk_B @ sk_A))),
% 0.65/0.86      inference('sat_resolution*', [status(thm)], ['2', '12'])).
% 0.65/0.86  thf('14', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.65/0.86      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.65/0.86  thf(d4_xboole_0, axiom,
% 0.65/0.86    (![A:$i,B:$i,C:$i]:
% 0.65/0.86     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.65/0.86       ( ![D:$i]:
% 0.65/0.86         ( ( r2_hidden @ D @ C ) <=>
% 0.65/0.86           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.65/0.86  thf('15', plain,
% 0.65/0.86      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.65/0.86         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.65/0.86          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.65/0.86          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.65/0.86      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.65/0.86  thf('16', plain,
% 0.65/0.86      (![X31 : $i, X33 : $i, X34 : $i]:
% 0.65/0.86         (~ (r2_hidden @ X34 @ X33)
% 0.65/0.86          | ((X34) = (X31))
% 0.65/0.86          | ((X33) != (k1_tarski @ X31)))),
% 0.65/0.86      inference('cnf', [status(esa)], [d1_tarski])).
% 0.65/0.86  thf('17', plain,
% 0.65/0.86      (![X31 : $i, X34 : $i]:
% 0.65/0.86         (((X34) = (X31)) | ~ (r2_hidden @ X34 @ (k1_tarski @ X31)))),
% 0.65/0.86      inference('simplify', [status(thm)], ['16'])).
% 0.65/0.86  thf('18', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.86         ((r2_hidden @ (sk_D @ X2 @ (k1_tarski @ X0) @ X1) @ X2)
% 0.65/0.86          | ((X2) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.65/0.86          | ((sk_D @ X2 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['15', '17'])).
% 0.65/0.86  thf(t3_boole, axiom,
% 0.65/0.86    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.65/0.86  thf('19', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.65/0.86      inference('cnf', [status(esa)], [t3_boole])).
% 0.65/0.86  thf('20', plain,
% 0.65/0.86      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.65/0.86         (~ (r2_hidden @ X12 @ X10)
% 0.65/0.86          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.65/0.86      inference('simplify', [status(thm)], ['8'])).
% 0.65/0.86  thf('21', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.65/0.86      inference('sup-', [status(thm)], ['19', '20'])).
% 0.65/0.86  thf('22', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.65/0.86      inference('condensation', [status(thm)], ['21'])).
% 0.65/0.86  thf('23', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         (((sk_D @ k1_xboole_0 @ (k1_tarski @ X1) @ X0) = (X1))
% 0.65/0.86          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k1_tarski @ X1))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['18', '22'])).
% 0.65/0.86  thf('24', plain,
% 0.65/0.86      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.65/0.86         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.65/0.86          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.65/0.86          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.65/0.86      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.65/0.86  thf('25', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.65/0.86      inference('condensation', [status(thm)], ['21'])).
% 0.65/0.86  thf('26', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.65/0.86          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['24', '25'])).
% 0.65/0.86  thf('27', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         ((r2_hidden @ X0 @ X1)
% 0.65/0.86          | ((k1_xboole_0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.65/0.86          | ((k1_xboole_0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 0.65/0.86      inference('sup+', [status(thm)], ['23', '26'])).
% 0.65/0.86  thf('28', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         (((k1_xboole_0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.65/0.86          | (r2_hidden @ X0 @ X1))),
% 0.65/0.86      inference('simplify', [status(thm)], ['27'])).
% 0.65/0.86  thf(t100_xboole_1, axiom,
% 0.65/0.86    (![A:$i,B:$i]:
% 0.65/0.86     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.65/0.86  thf('29', plain,
% 0.65/0.86      (![X16 : $i, X17 : $i]:
% 0.65/0.86         ((k4_xboole_0 @ X16 @ X17)
% 0.65/0.86           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.65/0.86      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.65/0.86  thf('30', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.65/0.86            = (k5_xboole_0 @ X1 @ k1_xboole_0))
% 0.65/0.86          | (r2_hidden @ X0 @ X1))),
% 0.65/0.86      inference('sup+', [status(thm)], ['28', '29'])).
% 0.65/0.86  thf('31', plain,
% 0.65/0.86      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.65/0.86         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.65/0.86          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.65/0.86          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.65/0.86      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.65/0.86  thf('32', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.65/0.86          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.65/0.86      inference('eq_fact', [status(thm)], ['31'])).
% 0.65/0.86  thf('33', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.65/0.86      inference('condensation', [status(thm)], ['21'])).
% 0.65/0.86  thf('34', plain,
% 0.65/0.86      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.65/0.86      inference('sup-', [status(thm)], ['32', '33'])).
% 0.65/0.86  thf('35', plain,
% 0.65/0.86      (![X16 : $i, X17 : $i]:
% 0.65/0.86         ((k4_xboole_0 @ X16 @ X17)
% 0.65/0.86           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.65/0.86      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.65/0.86  thf('36', plain,
% 0.65/0.86      (![X0 : $i]:
% 0.65/0.86         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.65/0.86      inference('sup+', [status(thm)], ['34', '35'])).
% 0.65/0.86  thf('37', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.65/0.86      inference('cnf', [status(esa)], [t3_boole])).
% 0.65/0.86  thf('38', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.65/0.86      inference('sup+', [status(thm)], ['36', '37'])).
% 0.65/0.86  thf('39', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1))
% 0.65/0.86          | (r2_hidden @ X0 @ X1))),
% 0.65/0.86      inference('demod', [status(thm)], ['30', '38'])).
% 0.65/0.86  thf('40', plain,
% 0.65/0.86      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 0.65/0.86         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.65/0.86      inference('split', [status(esa)], ['3'])).
% 0.65/0.86  thf('41', plain,
% 0.65/0.86      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 0.65/0.86       ((r2_hidden @ sk_B @ sk_A))),
% 0.65/0.86      inference('split', [status(esa)], ['3'])).
% 0.65/0.86  thf('42', plain, (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.65/0.86      inference('sat_resolution*', [status(thm)], ['2', '12', '41'])).
% 0.65/0.86  thf('43', plain, (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A))),
% 0.65/0.86      inference('simpl_trail', [status(thm)], ['40', '42'])).
% 0.65/0.86  thf('44', plain, ((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 0.65/0.86      inference('sup-', [status(thm)], ['39', '43'])).
% 0.65/0.86  thf('45', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.65/0.86      inference('simplify', [status(thm)], ['44'])).
% 0.65/0.86  thf('46', plain, ($false), inference('demod', [status(thm)], ['14', '45'])).
% 0.65/0.86  
% 0.65/0.86  % SZS output end Refutation
% 0.65/0.86  
% 0.65/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
