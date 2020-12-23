%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tutsLWUWft

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 141 expanded)
%              Number of leaves         :   21 (  45 expanded)
%              Depth                    :   14
%              Number of atoms          :  478 (1144 expanded)
%              Number of equality atoms :   62 ( 158 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('0',plain,(
    ! [X51: $i,X52: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X51 ) @ X52 )
      | ( r2_hidden @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t20_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
      <=> ( A != B ) ) ),
    inference('cnf.neg',[status(esa)],[t20_zfmisc_1])).

thf('5',plain,
    ( ( sk_A = sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( sk_A != sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( sk_A != sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( X9 != X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X10: $i] :
      ( r1_tarski @ X10 @ X10 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X12: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X14 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_A = sk_B_1 )
   <= ( sk_A = sk_B_1 ) ),
    inference(split,[status(esa)],['5'])).

thf('14',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf('15',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_A = sk_B_1 )
   <= ( sk_A = sk_B_1 ) ),
    inference(split,[status(esa)],['5'])).

thf('17',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_B_1 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B_1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_B_1 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('19',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( X37 != X36 )
      | ( r2_hidden @ X37 @ X38 )
      | ( X38
       != ( k1_tarski @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('20',plain,(
    ! [X36: $i] :
      ( r2_hidden @ X36 @ ( k1_tarski @ X36 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( r2_hidden @ sk_B_1 @ k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['18','20'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('22',plain,(
    ! [X18: $i] :
      ( r1_xboole_0 @ X18 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('23',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('24',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X18: $i] :
      ( r1_xboole_0 @ X18 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A != sk_B_1 ) ),
    inference('sup-',[status(thm)],['21','34'])).

thf('36',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_B_1 ) ),
    inference(split,[status(esa)],['5'])).

thf('37',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['8','35','36'])).

thf('38',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['6','37'])).

thf('39',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','38'])).

thf('40',plain,(
    r2_hidden @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X36: $i,X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X39 @ X38 )
      | ( X39 = X36 )
      | ( X38
       != ( k1_tarski @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('42',plain,(
    ! [X36: $i,X39: $i] :
      ( ( X39 = X36 )
      | ~ ( r2_hidden @ X39 @ ( k1_tarski @ X36 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    sk_B_1 = sk_A ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,
    ( ( sk_A != sk_B_1 )
   <= ( sk_A != sk_B_1 ) ),
    inference(split,[status(esa)],['7'])).

thf('45',plain,(
    sk_A != sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['8','35'])).

thf('46',plain,(
    sk_A != sk_B_1 ),
    inference(simpl_trail,[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['43','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tutsLWUWft
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:45:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 196 iterations in 0.067s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(l27_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      (![X51 : $i, X52 : $i]:
% 0.22/0.49         ((r1_xboole_0 @ (k1_tarski @ X51) @ X52) | (r2_hidden @ X51 @ X52))),
% 0.22/0.49      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.22/0.49  thf(symmetry_r1_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X2 : $i, X3 : $i]:
% 0.22/0.49         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.22/0.49      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf(t83_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X21 : $i, X22 : $i]:
% 0.22/0.49         (((k4_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_xboole_0 @ X21 @ X22))),
% 0.22/0.49      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((r2_hidden @ X0 @ X1)
% 0.22/0.49          | ((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.49  thf(t20_zfmisc_1, conjecture,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.49         ( k1_tarski @ A ) ) <=>
% 0.22/0.49       ( ( A ) != ( B ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i]:
% 0.22/0.49        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.49            ( k1_tarski @ A ) ) <=>
% 0.22/0.49          ( ( A ) != ( B ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t20_zfmisc_1])).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      ((((sk_A) = (sk_B_1))
% 0.22/0.49        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.22/0.49            != (k1_tarski @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.22/0.49          != (k1_tarski @ sk_A)))
% 0.22/0.49         <= (~
% 0.22/0.49             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.22/0.49                = (k1_tarski @ sk_A))))),
% 0.22/0.49      inference('split', [status(esa)], ['5'])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      ((((sk_A) != (sk_B_1))
% 0.22/0.49        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.22/0.49            = (k1_tarski @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (~ (((sk_A) = (sk_B_1))) | 
% 0.22/0.49       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.22/0.49          = (k1_tarski @ sk_A)))),
% 0.22/0.49      inference('split', [status(esa)], ['7'])).
% 0.22/0.49  thf(d10_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (![X9 : $i, X10 : $i]: ((r1_tarski @ X9 @ X10) | ((X9) != (X10)))),
% 0.22/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.49  thf('10', plain, (![X10 : $i]: (r1_tarski @ X10 @ X10)),
% 0.22/0.49      inference('simplify', [status(thm)], ['9'])).
% 0.22/0.49  thf(l32_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (![X12 : $i, X14 : $i]:
% 0.22/0.49         (((k4_xboole_0 @ X12 @ X14) = (k1_xboole_0))
% 0.22/0.49          | ~ (r1_tarski @ X12 @ X14))),
% 0.22/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.22/0.49  thf('12', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.49  thf('13', plain, ((((sk_A) = (sk_B_1))) <= ((((sk_A) = (sk_B_1))))),
% 0.22/0.49      inference('split', [status(esa)], ['5'])).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.22/0.49          = (k1_tarski @ sk_A)))
% 0.22/0.49         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.22/0.49                = (k1_tarski @ sk_A))))),
% 0.22/0.49      inference('split', [status(esa)], ['7'])).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      ((((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_B_1))
% 0.22/0.49          = (k1_tarski @ sk_A)))
% 0.22/0.49         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.22/0.49                = (k1_tarski @ sk_A))) & 
% 0.22/0.49             (((sk_A) = (sk_B_1))))),
% 0.22/0.49      inference('sup+', [status(thm)], ['13', '14'])).
% 0.22/0.49  thf('16', plain, ((((sk_A) = (sk_B_1))) <= ((((sk_A) = (sk_B_1))))),
% 0.22/0.49      inference('split', [status(esa)], ['5'])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      ((((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_B_1))
% 0.22/0.49          = (k1_tarski @ sk_B_1)))
% 0.22/0.49         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.22/0.49                = (k1_tarski @ sk_A))) & 
% 0.22/0.49             (((sk_A) = (sk_B_1))))),
% 0.22/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      ((((k1_xboole_0) = (k1_tarski @ sk_B_1)))
% 0.22/0.49         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.22/0.49                = (k1_tarski @ sk_A))) & 
% 0.22/0.49             (((sk_A) = (sk_B_1))))),
% 0.22/0.49      inference('sup+', [status(thm)], ['12', '17'])).
% 0.22/0.49  thf(d1_tarski, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.22/0.49         (((X37) != (X36))
% 0.22/0.49          | (r2_hidden @ X37 @ X38)
% 0.22/0.49          | ((X38) != (k1_tarski @ X36)))),
% 0.22/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.49  thf('20', plain, (![X36 : $i]: (r2_hidden @ X36 @ (k1_tarski @ X36))),
% 0.22/0.49      inference('simplify', [status(thm)], ['19'])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      (((r2_hidden @ sk_B_1 @ k1_xboole_0))
% 0.22/0.49         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.22/0.49                = (k1_tarski @ sk_A))) & 
% 0.22/0.49             (((sk_A) = (sk_B_1))))),
% 0.22/0.49      inference('sup+', [status(thm)], ['18', '20'])).
% 0.22/0.49  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.22/0.49  thf('22', plain, (![X18 : $i]: (r1_xboole_0 @ X18 @ k1_xboole_0)),
% 0.22/0.49      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.22/0.49  thf(t7_xboole_0, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.49  thf('23', plain,
% 0.22/0.49      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.22/0.49      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.49  thf(t4_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.49            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.22/0.49          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.22/0.49      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.49  thf('26', plain,
% 0.22/0.49      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['22', '25'])).
% 0.22/0.49  thf(commutativity_k3_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.22/0.49          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.22/0.49      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.22/0.49          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.49  thf('30', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['26', '29'])).
% 0.22/0.49  thf('31', plain, (![X18 : $i]: (r1_xboole_0 @ X18 @ k1_xboole_0)),
% 0.22/0.49      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.22/0.49  thf('32', plain,
% 0.22/0.49      (![X2 : $i, X3 : $i]:
% 0.22/0.49         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.22/0.49      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.22/0.49  thf('33', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.22/0.49      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.49  thf('34', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.22/0.49      inference('demod', [status(thm)], ['30', '33'])).
% 0.22/0.49  thf('35', plain,
% 0.22/0.49      (~
% 0.22/0.49       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.22/0.49          = (k1_tarski @ sk_A))) | 
% 0.22/0.49       ~ (((sk_A) = (sk_B_1)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['21', '34'])).
% 0.22/0.49  thf('36', plain,
% 0.22/0.49      (~
% 0.22/0.49       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.22/0.49          = (k1_tarski @ sk_A))) | 
% 0.22/0.49       (((sk_A) = (sk_B_1)))),
% 0.22/0.49      inference('split', [status(esa)], ['5'])).
% 0.22/0.49  thf('37', plain,
% 0.22/0.49      (~
% 0.22/0.49       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.22/0.49          = (k1_tarski @ sk_A)))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['8', '35', '36'])).
% 0.22/0.49  thf('38', plain,
% 0.22/0.49      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.22/0.49         != (k1_tarski @ sk_A))),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['6', '37'])).
% 0.22/0.49  thf('39', plain,
% 0.22/0.49      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.22/0.49        | (r2_hidden @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['4', '38'])).
% 0.22/0.49  thf('40', plain, ((r2_hidden @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.22/0.49      inference('simplify', [status(thm)], ['39'])).
% 0.22/0.49  thf('41', plain,
% 0.22/0.49      (![X36 : $i, X38 : $i, X39 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X39 @ X38)
% 0.22/0.49          | ((X39) = (X36))
% 0.22/0.49          | ((X38) != (k1_tarski @ X36)))),
% 0.22/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.49  thf('42', plain,
% 0.22/0.49      (![X36 : $i, X39 : $i]:
% 0.22/0.49         (((X39) = (X36)) | ~ (r2_hidden @ X39 @ (k1_tarski @ X36)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['41'])).
% 0.22/0.49  thf('43', plain, (((sk_B_1) = (sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['40', '42'])).
% 0.22/0.49  thf('44', plain, ((((sk_A) != (sk_B_1))) <= (~ (((sk_A) = (sk_B_1))))),
% 0.22/0.49      inference('split', [status(esa)], ['7'])).
% 0.22/0.49  thf('45', plain, (~ (((sk_A) = (sk_B_1)))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['8', '35'])).
% 0.22/0.49  thf('46', plain, (((sk_A) != (sk_B_1))),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['44', '45'])).
% 0.22/0.49  thf('47', plain, ($false),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['43', '46'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
