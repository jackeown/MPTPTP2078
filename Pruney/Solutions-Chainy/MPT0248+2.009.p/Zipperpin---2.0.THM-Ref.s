%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zw91IRxEHE

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 162 expanded)
%              Number of leaves         :   17 (  48 expanded)
%              Depth                    :   15
%              Number of atoms          :  470 (1996 expanded)
%              Number of equality atoms :   96 ( 452 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_tarski @ X17 @ X16 )
      = ( k2_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X34 @ X35 ) )
      = ( k2_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X34 @ X35 ) )
      = ( k2_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('10',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X32
        = ( k2_tarski @ X30 @ X31 ) )
      | ( X32
        = ( k1_tarski @ X31 ) )
      | ( X32
        = ( k1_tarski @ X30 ) )
      | ( X32 = k1_xboole_0 )
      | ~ ( r1_tarski @ X32 @ ( k2_tarski @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_C
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('19',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('23',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('25',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('31',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['18','20','32'])).

thf('34',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['17','33'])).

thf('35',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('36',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('38',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('39',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('43',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['17','33'])).

thf('44',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_C != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['26'])).

thf('46',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['44','45'])).

thf('47',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['35','46'])).

thf('48',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['15','34','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zw91IRxEHE
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:33:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 191 iterations in 0.072s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(t43_zfmisc_1, conjecture,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.21/0.53          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.53          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.53          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.53        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.21/0.53             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.53             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.53             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.21/0.53  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(commutativity_k2_tarski, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X16 : $i, X17 : $i]:
% 0.21/0.53         ((k2_tarski @ X17 @ X16) = (k2_tarski @ X16 @ X17))),
% 0.21/0.53      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.53  thf(l51_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X34 : $i, X35 : $i]:
% 0.21/0.53         ((k3_tarski @ (k2_tarski @ X34 @ X35)) = (k2_xboole_0 @ X34 @ X35))),
% 0.21/0.53      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.53      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X34 : $i, X35 : $i]:
% 0.21/0.53         ((k3_tarski @ (k2_tarski @ X34 @ X35)) = (k2_xboole_0 @ X34 @ X35))),
% 0.21/0.53      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.53      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.53  thf(t7_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.21/0.53      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.53  thf('8', plain, ((r1_tarski @ sk_C @ (k1_tarski @ sk_A))),
% 0.21/0.53      inference('sup+', [status(thm)], ['0', '7'])).
% 0.21/0.53  thf(t69_enumset1, axiom,
% 0.21/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.53  thf('9', plain, (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.21/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.53  thf(l45_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.21/0.53       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.21/0.53            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.21/0.53         (((X32) = (k2_tarski @ X30 @ X31))
% 0.21/0.53          | ((X32) = (k1_tarski @ X31))
% 0.21/0.53          | ((X32) = (k1_tarski @ X30))
% 0.21/0.53          | ((X32) = (k1_xboole_0))
% 0.21/0.53          | ~ (r1_tarski @ X32 @ (k2_tarski @ X30 @ X31)))),
% 0.21/0.53      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.21/0.53          | ((X1) = (k1_xboole_0))
% 0.21/0.53          | ((X1) = (k1_tarski @ X0))
% 0.21/0.53          | ((X1) = (k1_tarski @ X0))
% 0.21/0.53          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.21/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.21/0.53          | ((X1) = (k1_xboole_0))
% 0.21/0.53          | ((X1) = (k1_tarski @ X0))
% 0.21/0.53          | ((X1) = (k1_tarski @ X0))
% 0.21/0.53          | ((X1) = (k1_tarski @ X0)))),
% 0.21/0.53      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (((X1) = (k1_tarski @ X0))
% 0.21/0.53          | ((X1) = (k1_xboole_0))
% 0.21/0.53          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      ((((sk_C) = (k1_xboole_0)) | ((sk_C) = (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['8', '14'])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      ((((sk_B) != (k1_xboole_0)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      ((((sk_C) != (k1_tarski @ sk_A))) <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('split', [status(esa)], ['16'])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.21/0.53      inference('split', [status(esa)], ['16'])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('split', [status(esa)], ['19'])).
% 0.21/0.53  thf('21', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.21/0.53      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.53  thf('23', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.21/0.53      inference('sup+', [status(thm)], ['21', '22'])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (((X1) = (k1_tarski @ X0))
% 0.21/0.53          | ((X1) = (k1_xboole_0))
% 0.21/0.53          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('split', [status(esa)], ['26'])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.21/0.53         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['25', '27'])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.21/0.53      inference('split', [status(esa)], ['16'])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      ((((sk_B) != (sk_B)))
% 0.21/0.53         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['31'])).
% 0.21/0.53  thf('33', plain, (~ (((sk_C) = (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['18', '20', '32'])).
% 0.21/0.53  thf('34', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['17', '33'])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.21/0.53      inference('split', [status(esa)], ['26'])).
% 0.21/0.53  thf('36', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.53  thf('38', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.21/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.53  thf(t12_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i]:
% 0.21/0.53         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 0.21/0.53      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.53  thf('40', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      ((![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0)))
% 0.21/0.53         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('sup+', [status(thm)], ['37', '40'])).
% 0.21/0.53  thf('42', plain,
% 0.21/0.53      ((((k1_tarski @ sk_A) = (sk_C))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('sup+', [status(thm)], ['36', '41'])).
% 0.21/0.53  thf('43', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['17', '33'])).
% 0.21/0.53  thf('44', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      (~ (((sk_C) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('split', [status(esa)], ['26'])).
% 0.21/0.53  thf('46', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['44', '45'])).
% 0.21/0.53  thf('47', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['35', '46'])).
% 0.21/0.53  thf('48', plain, ($false),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['15', '34', '47'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
