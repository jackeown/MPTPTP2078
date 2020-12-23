%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1aloFkuJjO

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:57 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 108 expanded)
%              Number of leaves         :    9 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :  463 (1101 expanded)
%              Number of equality atoms :   46 ( 104 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( X18 != X17 )
      | ( r2_hidden @ X18 @ X19 )
      | ( X19
       != ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('6',plain,(
    ! [X17: $i] :
      ( r2_hidden @ X17 @ ( k1_tarski @ X17 ) ) ),
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
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('9',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
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

thf('15',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['15'])).

thf('17',plain,(
    ! [X17: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ( X20 = X17 )
      | ( X19
       != ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('18',plain,(
    ! [X17: $i,X20: $i] :
      ( ( X20 = X17 )
      | ~ ( r2_hidden @ X20 @ ( k1_tarski @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['15'])).

thf('21',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['15'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['15'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('30',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','33'])).

thf('35',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('36',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('37',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['2','12','36'])).

thf('38',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['35','37'])).

thf('39',plain,
    ( ( sk_A != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['14','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1aloFkuJjO
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:56:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.05/1.25  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.05/1.25  % Solved by: fo/fo7.sh
% 1.05/1.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.25  % done 1140 iterations in 0.777s
% 1.05/1.25  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.05/1.25  % SZS output start Refutation
% 1.05/1.25  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.25  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.05/1.25  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.05/1.25  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.05/1.25  thf(sk_B_type, type, sk_B: $i).
% 1.05/1.25  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.05/1.25  thf(t65_zfmisc_1, conjecture,
% 1.05/1.25    (![A:$i,B:$i]:
% 1.05/1.25     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.05/1.25       ( ~( r2_hidden @ B @ A ) ) ))).
% 1.05/1.25  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.25    (~( ![A:$i,B:$i]:
% 1.05/1.25        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.05/1.25          ( ~( r2_hidden @ B @ A ) ) ) )),
% 1.05/1.25    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 1.05/1.25  thf('0', plain,
% 1.05/1.25      ((~ (r2_hidden @ sk_B @ sk_A)
% 1.05/1.25        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('1', plain,
% 1.05/1.25      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 1.05/1.25      inference('split', [status(esa)], ['0'])).
% 1.05/1.25  thf('2', plain,
% 1.05/1.25      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 1.05/1.25       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.05/1.25      inference('split', [status(esa)], ['0'])).
% 1.05/1.25  thf('3', plain,
% 1.05/1.25      (((r2_hidden @ sk_B @ sk_A)
% 1.05/1.25        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('4', plain,
% 1.05/1.25      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 1.05/1.25      inference('split', [status(esa)], ['3'])).
% 1.05/1.25  thf(d1_tarski, axiom,
% 1.05/1.25    (![A:$i,B:$i]:
% 1.05/1.25     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.05/1.25       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.05/1.25  thf('5', plain,
% 1.05/1.25      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.05/1.25         (((X18) != (X17))
% 1.05/1.25          | (r2_hidden @ X18 @ X19)
% 1.05/1.25          | ((X19) != (k1_tarski @ X17)))),
% 1.05/1.25      inference('cnf', [status(esa)], [d1_tarski])).
% 1.05/1.25  thf('6', plain, (![X17 : $i]: (r2_hidden @ X17 @ (k1_tarski @ X17))),
% 1.05/1.25      inference('simplify', [status(thm)], ['5'])).
% 1.05/1.25  thf('7', plain,
% 1.05/1.25      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 1.05/1.25         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.05/1.25      inference('split', [status(esa)], ['0'])).
% 1.05/1.25  thf(d5_xboole_0, axiom,
% 1.05/1.25    (![A:$i,B:$i,C:$i]:
% 1.05/1.25     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.05/1.25       ( ![D:$i]:
% 1.05/1.25         ( ( r2_hidden @ D @ C ) <=>
% 1.05/1.25           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.05/1.25  thf('8', plain,
% 1.05/1.25      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.05/1.25         (~ (r2_hidden @ X6 @ X5)
% 1.05/1.25          | ~ (r2_hidden @ X6 @ X4)
% 1.05/1.25          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.05/1.25      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.05/1.25  thf('9', plain,
% 1.05/1.25      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.05/1.25         (~ (r2_hidden @ X6 @ X4)
% 1.05/1.25          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.05/1.25      inference('simplify', [status(thm)], ['8'])).
% 1.05/1.25  thf('10', plain,
% 1.05/1.25      ((![X0 : $i]:
% 1.05/1.25          (~ (r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))))
% 1.05/1.25         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.05/1.25      inference('sup-', [status(thm)], ['7', '9'])).
% 1.05/1.25  thf('11', plain,
% 1.05/1.25      ((~ (r2_hidden @ sk_B @ sk_A))
% 1.05/1.25         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.05/1.25      inference('sup-', [status(thm)], ['6', '10'])).
% 1.05/1.25  thf('12', plain,
% 1.05/1.25      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 1.05/1.25       ~ ((r2_hidden @ sk_B @ sk_A))),
% 1.05/1.25      inference('sup-', [status(thm)], ['4', '11'])).
% 1.05/1.25  thf('13', plain, (~ ((r2_hidden @ sk_B @ sk_A))),
% 1.05/1.25      inference('sat_resolution*', [status(thm)], ['2', '12'])).
% 1.05/1.25  thf('14', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 1.05/1.25      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 1.05/1.25  thf('15', plain,
% 1.05/1.25      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.05/1.25         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 1.05/1.25          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 1.05/1.25          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.05/1.25      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.05/1.25  thf('16', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.05/1.25          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.05/1.25      inference('eq_fact', [status(thm)], ['15'])).
% 1.05/1.25  thf('17', plain,
% 1.05/1.25      (![X17 : $i, X19 : $i, X20 : $i]:
% 1.05/1.25         (~ (r2_hidden @ X20 @ X19)
% 1.05/1.25          | ((X20) = (X17))
% 1.05/1.25          | ((X19) != (k1_tarski @ X17)))),
% 1.05/1.25      inference('cnf', [status(esa)], [d1_tarski])).
% 1.05/1.25  thf('18', plain,
% 1.05/1.25      (![X17 : $i, X20 : $i]:
% 1.05/1.25         (((X20) = (X17)) | ~ (r2_hidden @ X20 @ (k1_tarski @ X17)))),
% 1.05/1.25      inference('simplify', [status(thm)], ['17'])).
% 1.05/1.25  thf('19', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         (((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.05/1.25          | ((sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['16', '18'])).
% 1.05/1.25  thf('20', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.05/1.25          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.05/1.25      inference('eq_fact', [status(thm)], ['15'])).
% 1.05/1.25  thf('21', plain,
% 1.05/1.25      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.05/1.25         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 1.05/1.25          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 1.05/1.25          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 1.05/1.25          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.05/1.25      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.05/1.25  thf('22', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 1.05/1.25          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.05/1.25          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 1.05/1.25          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['20', '21'])).
% 1.05/1.25  thf('23', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 1.05/1.25          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.05/1.25          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.05/1.25      inference('simplify', [status(thm)], ['22'])).
% 1.05/1.25  thf('24', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.05/1.25          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.05/1.25      inference('eq_fact', [status(thm)], ['15'])).
% 1.05/1.25  thf('25', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 1.05/1.25          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 1.05/1.25      inference('clc', [status(thm)], ['23', '24'])).
% 1.05/1.25  thf('26', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((r2_hidden @ X0 @ X1)
% 1.05/1.25          | ((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.05/1.25          | ((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.05/1.25      inference('sup+', [status(thm)], ['19', '25'])).
% 1.05/1.25  thf('27', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         (((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.05/1.25          | (r2_hidden @ X0 @ X1))),
% 1.05/1.25      inference('simplify', [status(thm)], ['26'])).
% 1.05/1.25  thf('28', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.05/1.25          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.05/1.25      inference('eq_fact', [status(thm)], ['15'])).
% 1.05/1.25  thf('29', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 1.05/1.25          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 1.05/1.25      inference('clc', [status(thm)], ['23', '24'])).
% 1.05/1.25  thf('30', plain,
% 1.05/1.25      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.05/1.25         (~ (r2_hidden @ X6 @ X4)
% 1.05/1.25          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.05/1.25      inference('simplify', [status(thm)], ['8'])).
% 1.05/1.25  thf('31', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.25         (((X2) = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 1.05/1.25          | ~ (r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 1.05/1.25      inference('sup-', [status(thm)], ['29', '30'])).
% 1.05/1.25  thf('32', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         (((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 1.05/1.25          | ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.05/1.25      inference('sup-', [status(thm)], ['28', '31'])).
% 1.05/1.25  thf('33', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.05/1.25      inference('simplify', [status(thm)], ['32'])).
% 1.05/1.25  thf('34', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         (((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.05/1.25          | (r2_hidden @ X0 @ X1))),
% 1.05/1.25      inference('sup+', [status(thm)], ['27', '33'])).
% 1.05/1.25  thf('35', plain,
% 1.05/1.25      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 1.05/1.25         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.05/1.25      inference('split', [status(esa)], ['3'])).
% 1.05/1.25  thf('36', plain,
% 1.05/1.25      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 1.05/1.25       ((r2_hidden @ sk_B @ sk_A))),
% 1.05/1.25      inference('split', [status(esa)], ['3'])).
% 1.05/1.25  thf('37', plain, (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.05/1.25      inference('sat_resolution*', [status(thm)], ['2', '12', '36'])).
% 1.05/1.25  thf('38', plain, (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A))),
% 1.05/1.25      inference('simpl_trail', [status(thm)], ['35', '37'])).
% 1.05/1.25  thf('39', plain, ((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 1.05/1.25      inference('sup-', [status(thm)], ['34', '38'])).
% 1.05/1.25  thf('40', plain, ((r2_hidden @ sk_B @ sk_A)),
% 1.05/1.25      inference('simplify', [status(thm)], ['39'])).
% 1.05/1.25  thf('41', plain, ($false), inference('demod', [status(thm)], ['14', '40'])).
% 1.05/1.25  
% 1.05/1.25  % SZS output end Refutation
% 1.05/1.25  
% 1.05/1.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
