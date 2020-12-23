%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Vg3lloLZQ4

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 153 expanded)
%              Number of leaves         :   19 (  45 expanded)
%              Depth                    :   15
%              Number of atoms          :  534 (1486 expanded)
%              Number of equality atoms :   70 ( 212 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('0',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X34 ) @ X35 )
      | ( r2_hidden @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_xboole_0 @ X16 @ X17 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X10: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X20 != X19 )
      | ( r2_hidden @ X20 @ X21 )
      | ( X21
       != ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('20',plain,(
    ! [X19: $i] :
      ( r2_hidden @ X19 @ ( k1_tarski @ X19 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( r2_hidden @ sk_B_1 @ k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['18','20'])).

thf('22',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf('23',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_xboole_0 @ X16 @ X18 )
      | ( ( k4_xboole_0 @ X16 @ X18 )
       != X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('24',plain,
    ( ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('26',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('27',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
        | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('33',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A != sk_B_1 ) ),
    inference('sup-',[status(thm)],['21','33'])).

thf('35',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_B_1 ) ),
    inference(split,[status(esa)],['5'])).

thf('36',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['8','34','35'])).

thf('37',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['6','36'])).

thf('38',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','37'])).

thf('39',plain,(
    r2_hidden @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X19: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X21 )
      | ( X22 = X19 )
      | ( X21
       != ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('41',plain,(
    ! [X19: $i,X22: $i] :
      ( ( X22 = X19 )
      | ~ ( r2_hidden @ X22 @ ( k1_tarski @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    sk_B_1 = sk_A ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,
    ( ( sk_A != sk_B_1 )
   <= ( sk_A != sk_B_1 ) ),
    inference(split,[status(esa)],['7'])).

thf('44',plain,(
    sk_A != sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['8','34'])).

thf('45',plain,(
    sk_A != sk_B_1 ),
    inference(simpl_trail,[status(thm)],['43','44'])).

thf('46',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['42','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Vg3lloLZQ4
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:46:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 95 iterations in 0.043s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(l27_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (![X34 : $i, X35 : $i]:
% 0.20/0.53         ((r1_xboole_0 @ (k1_tarski @ X34) @ X35) | (r2_hidden @ X34 @ X35))),
% 0.20/0.53      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.20/0.53  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.53      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.53  thf(t83_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X16 : $i, X17 : $i]:
% 0.20/0.53         (((k4_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_xboole_0 @ X16 @ X17))),
% 0.20/0.53      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((r2_hidden @ X0 @ X1)
% 0.20/0.53          | ((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf(t20_zfmisc_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.53         ( k1_tarski @ A ) ) <=>
% 0.20/0.53       ( ( A ) != ( B ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i]:
% 0.20/0.53        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.53            ( k1_tarski @ A ) ) <=>
% 0.20/0.53          ( ( A ) != ( B ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      ((((sk_A) = (sk_B_1))
% 0.20/0.53        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.20/0.53            != (k1_tarski @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.20/0.53          != (k1_tarski @ sk_A)))
% 0.20/0.53         <= (~
% 0.20/0.53             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.20/0.53                = (k1_tarski @ sk_A))))),
% 0.20/0.53      inference('split', [status(esa)], ['5'])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      ((((sk_A) != (sk_B_1))
% 0.20/0.53        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.20/0.53            = (k1_tarski @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (~ (((sk_A) = (sk_B_1))) | 
% 0.20/0.53       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.20/0.53          = (k1_tarski @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['7'])).
% 0.20/0.53  thf(d10_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.53  thf('10', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.20/0.53      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.53  thf(l32_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X10 : $i, X12 : $i]:
% 0.20/0.53         (((k4_xboole_0 @ X10 @ X12) = (k1_xboole_0))
% 0.20/0.53          | ~ (r1_tarski @ X10 @ X12))),
% 0.20/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.53  thf('12', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.53  thf('13', plain, ((((sk_A) = (sk_B_1))) <= ((((sk_A) = (sk_B_1))))),
% 0.20/0.53      inference('split', [status(esa)], ['5'])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.20/0.53          = (k1_tarski @ sk_A)))
% 0.20/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.20/0.53                = (k1_tarski @ sk_A))))),
% 0.20/0.53      inference('split', [status(esa)], ['7'])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      ((((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_B_1))
% 0.20/0.53          = (k1_tarski @ sk_A)))
% 0.20/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.20/0.53                = (k1_tarski @ sk_A))) & 
% 0.20/0.53             (((sk_A) = (sk_B_1))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf('16', plain, ((((sk_A) = (sk_B_1))) <= ((((sk_A) = (sk_B_1))))),
% 0.20/0.53      inference('split', [status(esa)], ['5'])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      ((((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_B_1))
% 0.20/0.53          = (k1_tarski @ sk_B_1)))
% 0.20/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.20/0.53                = (k1_tarski @ sk_A))) & 
% 0.20/0.53             (((sk_A) = (sk_B_1))))),
% 0.20/0.53      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      ((((k1_xboole_0) = (k1_tarski @ sk_B_1)))
% 0.20/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.20/0.53                = (k1_tarski @ sk_A))) & 
% 0.20/0.53             (((sk_A) = (sk_B_1))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['12', '17'])).
% 0.20/0.53  thf(d1_tarski, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.53         (((X20) != (X19))
% 0.20/0.53          | (r2_hidden @ X20 @ X21)
% 0.20/0.53          | ((X21) != (k1_tarski @ X19)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.53  thf('20', plain, (![X19 : $i]: (r2_hidden @ X19 @ (k1_tarski @ X19))),
% 0.20/0.53      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (((r2_hidden @ sk_B_1 @ k1_xboole_0))
% 0.20/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.20/0.53                = (k1_tarski @ sk_A))) & 
% 0.20/0.53             (((sk_A) = (sk_B_1))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['18', '20'])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.20/0.53          = (k1_tarski @ sk_A)))
% 0.20/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.20/0.53                = (k1_tarski @ sk_A))))),
% 0.20/0.53      inference('split', [status(esa)], ['7'])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (![X16 : $i, X18 : $i]:
% 0.20/0.53         ((r1_xboole_0 @ X16 @ X18) | ((k4_xboole_0 @ X16 @ X18) != (X16)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.20/0.53         | (r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))))
% 0.20/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.20/0.53                = (k1_tarski @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (((r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1)))
% 0.20/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.20/0.53                = (k1_tarski @ sk_A))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.53  thf(t7_xboole_0, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.53  thf(t4_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.53            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.53       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.53            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.20/0.53          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.20/0.53          = (k1_xboole_0)))
% 0.20/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.20/0.53                = (k1_tarski @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['25', '28'])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.20/0.53          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.20/0.53           | ~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))))
% 0.20/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.20/0.53                = (k1_tarski @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (((r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1)))
% 0.20/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.20/0.53                = (k1_tarski @ sk_A))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      ((![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0))
% 0.20/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.20/0.53                = (k1_tarski @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (~
% 0.20/0.53       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.20/0.53          = (k1_tarski @ sk_A))) | 
% 0.20/0.53       ~ (((sk_A) = (sk_B_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['21', '33'])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (~
% 0.20/0.53       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.20/0.53          = (k1_tarski @ sk_A))) | 
% 0.20/0.53       (((sk_A) = (sk_B_1)))),
% 0.20/0.53      inference('split', [status(esa)], ['5'])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (~
% 0.20/0.53       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.20/0.53          = (k1_tarski @ sk_A)))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['8', '34', '35'])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.20/0.53         != (k1_tarski @ sk_A))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['6', '36'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.20/0.53        | (r2_hidden @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['4', '37'])).
% 0.20/0.53  thf('39', plain, ((r2_hidden @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.20/0.53      inference('simplify', [status(thm)], ['38'])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (![X19 : $i, X21 : $i, X22 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X22 @ X21)
% 0.20/0.53          | ((X22) = (X19))
% 0.20/0.53          | ((X21) != (k1_tarski @ X19)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (![X19 : $i, X22 : $i]:
% 0.20/0.53         (((X22) = (X19)) | ~ (r2_hidden @ X22 @ (k1_tarski @ X19)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.53  thf('42', plain, (((sk_B_1) = (sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['39', '41'])).
% 0.20/0.53  thf('43', plain, ((((sk_A) != (sk_B_1))) <= (~ (((sk_A) = (sk_B_1))))),
% 0.20/0.53      inference('split', [status(esa)], ['7'])).
% 0.20/0.53  thf('44', plain, (~ (((sk_A) = (sk_B_1)))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['8', '34'])).
% 0.20/0.53  thf('45', plain, (((sk_A) != (sk_B_1))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['43', '44'])).
% 0.20/0.53  thf('46', plain, ($false),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['42', '45'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
