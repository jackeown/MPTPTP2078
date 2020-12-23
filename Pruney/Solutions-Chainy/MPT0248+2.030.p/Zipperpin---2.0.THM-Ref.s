%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZO9COKGz0E

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:21 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 252 expanded)
%              Number of leaves         :   12 (  68 expanded)
%              Depth                    :   14
%              Number of atoms          :  477 (3542 expanded)
%              Number of equality atoms :   93 ( 796 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ ( k1_tarski @ X14 ) )
      | ( X13
       != ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('2',plain,(
    ! [X14: $i] :
      ( r1_tarski @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X14 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf('4',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ sk_C @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X13
        = ( k1_tarski @ X12 ) )
      | ( X13 = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_C
      = ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('19',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('20',plain,(
    r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('22',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['16'])).

thf('25',plain,
    ( ( sk_B
     != ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,
    ( ( sk_C
     != ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,
    ( ( sk_C != sk_C )
   <= ( ( sk_C
       != ( k1_tarski @ sk_A ) )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','35'])).

thf('37',plain,
    ( ( sk_B
      = ( k1_tarski @ sk_A ) )
    | ( sk_C
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('39',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['33'])).

thf('40',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['33'])).

thf('43',plain,
    ( ( sk_C != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['16'])).

thf('44',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['37','41','42','43'])).

thf('45',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['17','44'])).

thf('46',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['33'])).

thf('47',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( sk_C
     != ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['37','41','42','50'])).

thf('52',plain,(
    sk_C
 != ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['48','51'])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['15','45','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZO9COKGz0E
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:45:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 138 iterations in 0.047s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.49  thf(t43_zfmisc_1, conjecture,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.19/0.49          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.19/0.49          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.19/0.49          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.49        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.19/0.49             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.19/0.49             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.19/0.49             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.19/0.49  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(l3_zfmisc_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.19/0.49       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.19/0.49  thf('1', plain,
% 0.19/0.49      (![X13 : $i, X14 : $i]:
% 0.19/0.49         ((r1_tarski @ X13 @ (k1_tarski @ X14)) | ((X13) != (k1_tarski @ X14)))),
% 0.19/0.49      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      (![X14 : $i]: (r1_tarski @ (k1_tarski @ X14) @ (k1_tarski @ X14))),
% 0.19/0.49      inference('simplify', [status(thm)], ['1'])).
% 0.19/0.49  thf('3', plain,
% 0.19/0.49      ((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C) @ (k1_tarski @ sk_A))),
% 0.19/0.49      inference('sup+', [status(thm)], ['0', '2'])).
% 0.19/0.49  thf('4', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('5', plain,
% 0.19/0.49      ((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C) @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.49      inference('demod', [status(thm)], ['3', '4'])).
% 0.19/0.49  thf(commutativity_k2_xboole_0, axiom,
% 0.19/0.49    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.19/0.49  thf('6', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.49      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.19/0.49  thf(t11_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.19/0.49  thf('7', plain,
% 0.19/0.49      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.49         ((r1_tarski @ X2 @ X3) | ~ (r1_tarski @ (k2_xboole_0 @ X2 @ X4) @ X3))),
% 0.19/0.49      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.19/0.49  thf('8', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2) | (r1_tarski @ X0 @ X2))),
% 0.19/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.49  thf('9', plain, ((r1_tarski @ sk_C @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.49      inference('sup-', [status(thm)], ['5', '8'])).
% 0.19/0.49  thf('10', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('11', plain,
% 0.19/0.49      (![X12 : $i, X13 : $i]:
% 0.19/0.49         (((X13) = (k1_tarski @ X12))
% 0.19/0.49          | ((X13) = (k1_xboole_0))
% 0.19/0.49          | ~ (r1_tarski @ X13 @ (k1_tarski @ X12)))),
% 0.19/0.49      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.19/0.49  thf('12', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.19/0.49          | ((X0) = (k1_xboole_0))
% 0.19/0.49          | ((X0) = (k1_tarski @ sk_A)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.49  thf('13', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.19/0.49          | ((X0) = (k1_xboole_0))
% 0.19/0.49          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.19/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.19/0.49  thf('15', plain,
% 0.19/0.49      ((((sk_C) = (k2_xboole_0 @ sk_B @ sk_C)) | ((sk_C) = (k1_xboole_0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['9', '14'])).
% 0.19/0.49  thf('16', plain,
% 0.19/0.49      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_xboole_0)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('17', plain,
% 0.19/0.49      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.19/0.49      inference('split', [status(esa)], ['16'])).
% 0.19/0.49  thf('18', plain,
% 0.19/0.49      ((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C) @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.49      inference('demod', [status(thm)], ['3', '4'])).
% 0.19/0.49  thf('19', plain,
% 0.19/0.49      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.49         ((r1_tarski @ X2 @ X3) | ~ (r1_tarski @ (k2_xboole_0 @ X2 @ X4) @ X3))),
% 0.19/0.49      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.19/0.49  thf('20', plain, ((r1_tarski @ sk_B @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.49  thf('21', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.19/0.49          | ((X0) = (k1_xboole_0))
% 0.19/0.49          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.19/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.19/0.49  thf('22', plain,
% 0.19/0.49      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C)) | ((sk_B) = (k1_xboole_0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.49  thf('23', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('24', plain,
% 0.19/0.49      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.19/0.49      inference('split', [status(esa)], ['16'])).
% 0.19/0.49  thf('25', plain,
% 0.19/0.49      ((((sk_B) != (k2_xboole_0 @ sk_B @ sk_C)))
% 0.19/0.49         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.49  thf('26', plain,
% 0.19/0.49      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.19/0.49         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['22', '25'])).
% 0.19/0.49  thf('27', plain,
% 0.19/0.49      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.19/0.49      inference('simplify', [status(thm)], ['26'])).
% 0.19/0.49  thf('28', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.49      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.19/0.49  thf(t1_boole, axiom,
% 0.19/0.49    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.49  thf('29', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.19/0.49      inference('cnf', [status(esa)], [t1_boole])).
% 0.19/0.49  thf('30', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.19/0.49      inference('sup+', [status(thm)], ['28', '29'])).
% 0.19/0.49  thf('31', plain,
% 0.19/0.49      ((![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0)))
% 0.19/0.49         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.19/0.49      inference('sup+', [status(thm)], ['27', '30'])).
% 0.19/0.49  thf('32', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('33', plain,
% 0.19/0.49      ((((sk_B) != (k1_xboole_0)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('34', plain,
% 0.19/0.49      ((((sk_C) != (k1_tarski @ sk_A))) <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 0.19/0.49      inference('split', [status(esa)], ['33'])).
% 0.19/0.49  thf('35', plain,
% 0.19/0.49      ((((sk_C) != (k2_xboole_0 @ sk_B @ sk_C)))
% 0.19/0.49         <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['32', '34'])).
% 0.19/0.49  thf('36', plain,
% 0.19/0.49      ((((sk_C) != (sk_C)))
% 0.19/0.49         <= (~ (((sk_C) = (k1_tarski @ sk_A))) & 
% 0.19/0.49             ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['31', '35'])).
% 0.19/0.49  thf('37', plain,
% 0.19/0.49      ((((sk_B) = (k1_tarski @ sk_A))) | (((sk_C) = (k1_tarski @ sk_A)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['36'])).
% 0.19/0.49  thf('38', plain,
% 0.19/0.49      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.19/0.49      inference('simplify', [status(thm)], ['26'])).
% 0.19/0.49  thf('39', plain,
% 0.19/0.49      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.19/0.49      inference('split', [status(esa)], ['33'])).
% 0.19/0.49  thf('40', plain,
% 0.19/0.49      ((((sk_B) != (sk_B)))
% 0.19/0.49         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['38', '39'])).
% 0.19/0.49  thf('41', plain,
% 0.19/0.49      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['40'])).
% 0.19/0.49  thf('42', plain,
% 0.19/0.49      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.19/0.49      inference('split', [status(esa)], ['33'])).
% 0.19/0.49  thf('43', plain,
% 0.19/0.49      (~ (((sk_C) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.19/0.49      inference('split', [status(esa)], ['16'])).
% 0.19/0.49  thf('44', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 0.19/0.49      inference('sat_resolution*', [status(thm)], ['37', '41', '42', '43'])).
% 0.19/0.49  thf('45', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.49      inference('simpl_trail', [status(thm)], ['17', '44'])).
% 0.19/0.49  thf('46', plain,
% 0.19/0.49      ((((sk_C) != (k1_tarski @ sk_A))) <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 0.19/0.49      inference('split', [status(esa)], ['33'])).
% 0.19/0.49  thf('47', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('48', plain,
% 0.19/0.49      ((((sk_C) != (k2_xboole_0 @ sk_B @ sk_C)))
% 0.19/0.49         <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 0.19/0.49      inference('demod', [status(thm)], ['46', '47'])).
% 0.19/0.49  thf('49', plain,
% 0.19/0.49      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('50', plain,
% 0.19/0.49      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.19/0.49      inference('split', [status(esa)], ['49'])).
% 0.19/0.49  thf('51', plain, (~ (((sk_C) = (k1_tarski @ sk_A)))),
% 0.19/0.49      inference('sat_resolution*', [status(thm)], ['37', '41', '42', '50'])).
% 0.19/0.49  thf('52', plain, (((sk_C) != (k2_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.49      inference('simpl_trail', [status(thm)], ['48', '51'])).
% 0.19/0.49  thf('53', plain, ($false),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['15', '45', '52'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
