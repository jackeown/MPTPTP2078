%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YAD1ng96F7

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 169 expanded)
%              Number of leaves         :   22 (  54 expanded)
%              Depth                    :   17
%              Number of atoms          :  496 (1475 expanded)
%              Number of equality atoms :   25 (  95 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t205_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
        <=> ( ( k11_relat_1 @ B @ A )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t205_relat_1])).

thf('0',plain,
    ( ( ( k11_relat_1 @ sk_B_2 @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k11_relat_1 @ sk_B_2 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k11_relat_1 @ sk_B_2 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( ( k11_relat_1 @ sk_B_2 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_2 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('5',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( r2_hidden @ ( k4_tarski @ X15 @ ( sk_D_2 @ X15 @ X13 ) ) @ X13 )
      | ( X14
       != ( k1_relat_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('7',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X15 @ ( sk_D_2 @ X15 @ X13 ) ) @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_2 @ sk_A @ sk_B_2 ) ) @ sk_B_2 )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X20 @ X18 ) @ X19 )
      | ( r2_hidden @ X18 @ ( k11_relat_1 @ X19 @ X20 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('10',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_2 )
      | ( r2_hidden @ ( sk_D_2 @ sk_A @ sk_B_2 ) @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_A @ sk_B_2 ) @ ( k11_relat_1 @ sk_B_2 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_A @ sk_B_2 ) @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) )
      & ( ( k11_relat_1 @ sk_B_2 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['4','12'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('17',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('18',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) )
    | ( ( k11_relat_1 @ sk_B_2 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) )
    | ( ( k11_relat_1 @ sk_B_2 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference('sat_resolution*',[status(thm)],['3','19','20'])).

thf('22',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(simpl_trail,[status(thm)],['1','21'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('23',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ X8 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('24',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k11_relat_1 @ X19 @ X20 ) )
      | ( r2_hidden @ ( k4_tarski @ X20 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k11_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_B @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X13 )
      | ( r2_hidden @ X11 @ X14 )
      | ( X14
       != ( k1_relat_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('27',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X11 @ ( k1_relat_1 @ X13 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X13 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k11_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(simpl_trail,[status(thm)],['1','21'])).

thf('30',plain,
    ( ( v1_relat_1 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_relat_1 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t56_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf('33',plain,(
    ! [X21: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X21 ) @ ( sk_C_3 @ X21 ) ) @ X21 )
      | ( X21 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf('34',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k11_relat_1 @ X19 @ X20 ) )
      | ( r2_hidden @ ( k4_tarski @ X20 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k11_relat_1 @ X1 @ X0 ) )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k4_tarski @ ( sk_B_1 @ ( k11_relat_1 @ X1 @ X0 ) ) @ ( sk_C_3 @ ( k11_relat_1 @ X1 @ X0 ) ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k4_tarski @ ( sk_B_1 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ) @ ( sk_C_3 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ) ) ) @ sk_B_2 )
    | ~ ( v1_relat_1 @ sk_B_2 )
    | ( ( k11_relat_1 @ sk_B_2 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k4_tarski @ ( sk_B_1 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ) @ ( sk_C_3 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ) ) ) @ sk_B_2 )
    | ( ( k11_relat_1 @ sk_B_2 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k11_relat_1 @ sk_B_2 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_2 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('40',plain,(
    ( k11_relat_1 @ sk_B_2 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['3','19'])).

thf('41',plain,(
    ( k11_relat_1 @ sk_B_2 @ sk_A )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['39','40'])).

thf('42',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k4_tarski @ ( sk_B_1 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ) @ ( sk_C_3 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ) ) ) @ sk_B_2 ),
    inference('simplify_reflect-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X11 @ ( k1_relat_1 @ X13 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X13 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('44',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['22','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YAD1ng96F7
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:02:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 77 iterations in 0.051s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.51  thf(sk_C_3_type, type, sk_C_3: $i > $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.51  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.51  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.21/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.51  thf(t205_relat_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ B ) =>
% 0.21/0.51       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.21/0.51         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i]:
% 0.21/0.51        ( ( v1_relat_1 @ B ) =>
% 0.21/0.51          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.21/0.51            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      ((((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))
% 0.21/0.51        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))
% 0.21/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      ((((k11_relat_1 @ sk_B_2 @ sk_A) != (k1_xboole_0))
% 0.21/0.51        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (~ (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))) | 
% 0.21/0.51       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))),
% 0.21/0.51      inference('split', [status(esa)], ['2'])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      ((((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0)))
% 0.21/0.51         <= ((((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))
% 0.21/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.21/0.51      inference('split', [status(esa)], ['2'])).
% 0.21/0.51  thf(d4_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.21/0.51       ( ![C:$i]:
% 0.21/0.51         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.51           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X15 @ X14)
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X15 @ (sk_D_2 @ X15 @ X13)) @ X13)
% 0.21/0.51          | ((X14) != (k1_relat_1 @ X13)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X13 : $i, X15 : $i]:
% 0.21/0.51         ((r2_hidden @ (k4_tarski @ X15 @ (sk_D_2 @ X15 @ X13)) @ X13)
% 0.21/0.51          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X13)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_2 @ sk_A @ sk_B_2)) @ sk_B_2))
% 0.21/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['5', '7'])).
% 0.21/0.51  thf(t204_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ C ) =>
% 0.21/0.51       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.21/0.51         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.51         (~ (r2_hidden @ (k4_tarski @ X20 @ X18) @ X19)
% 0.21/0.51          | (r2_hidden @ X18 @ (k11_relat_1 @ X19 @ X20))
% 0.21/0.51          | ~ (v1_relat_1 @ X19))),
% 0.21/0.51      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (((~ (v1_relat_1 @ sk_B_2)
% 0.21/0.51         | (r2_hidden @ (sk_D_2 @ sk_A @ sk_B_2) @ 
% 0.21/0.51            (k11_relat_1 @ sk_B_2 @ sk_A))))
% 0.21/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.51  thf('11', plain, ((v1_relat_1 @ sk_B_2)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (((r2_hidden @ (sk_D_2 @ sk_A @ sk_B_2) @ (k11_relat_1 @ sk_B_2 @ sk_A)))
% 0.21/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.21/0.51      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (((r2_hidden @ (sk_D_2 @ sk_A @ sk_B_2) @ k1_xboole_0))
% 0.21/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))) & 
% 0.21/0.51             (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.51      inference('sup+', [status(thm)], ['4', '12'])).
% 0.21/0.51  thf(t2_boole, axiom,
% 0.21/0.51    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.51  thf(t4_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.51            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.51       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.51            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.21/0.51          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.51  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.51  thf('17', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.21/0.51      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.51  thf('18', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.21/0.51      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))) | 
% 0.21/0.51       ~ (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['13', '18'])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))) | 
% 0.21/0.51       (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('21', plain, (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['3', '19', '20'])).
% 0.21/0.51  thf('22', plain, (~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['1', '21'])).
% 0.21/0.51  thf(d1_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) <=>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ~( ( r2_hidden @ B @ A ) & 
% 0.21/0.51              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (![X8 : $i]: ((v1_relat_1 @ X8) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X18 @ (k11_relat_1 @ X19 @ X20))
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X20 @ X18) @ X19)
% 0.21/0.51          | ~ (v1_relat_1 @ X19))),
% 0.21/0.51      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v1_relat_1 @ (k11_relat_1 @ X1 @ X0))
% 0.21/0.51          | ~ (v1_relat_1 @ X1)
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X0 @ (sk_B @ (k11_relat_1 @ X1 @ X0))) @ 
% 0.21/0.51             X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.51         (~ (r2_hidden @ (k4_tarski @ X11 @ X12) @ X13)
% 0.21/0.51          | (r2_hidden @ X11 @ X14)
% 0.21/0.51          | ((X14) != (k1_relat_1 @ X13)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.51         ((r2_hidden @ X11 @ (k1_relat_1 @ X13))
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X11 @ X12) @ X13))),
% 0.21/0.51      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X0)
% 0.21/0.51          | (v1_relat_1 @ (k11_relat_1 @ X0 @ X1))
% 0.21/0.51          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['25', '27'])).
% 0.21/0.51  thf('29', plain, (~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['1', '21'])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (((v1_relat_1 @ (k11_relat_1 @ sk_B_2 @ sk_A)) | ~ (v1_relat_1 @ sk_B_2))),
% 0.21/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.51  thf('31', plain, ((v1_relat_1 @ sk_B_2)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('32', plain, ((v1_relat_1 @ (k11_relat_1 @ sk_B_2 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.51  thf(t56_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) =>
% 0.21/0.51       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.21/0.51         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      (![X21 : $i]:
% 0.21/0.51         ((r2_hidden @ (k4_tarski @ (sk_B_1 @ X21) @ (sk_C_3 @ X21)) @ X21)
% 0.21/0.51          | ((X21) = (k1_xboole_0))
% 0.21/0.51          | ~ (v1_relat_1 @ X21))),
% 0.21/0.51      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X18 @ (k11_relat_1 @ X19 @ X20))
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X20 @ X18) @ X19)
% 0.21/0.51          | ~ (v1_relat_1 @ X19))),
% 0.21/0.51      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ (k11_relat_1 @ X1 @ X0))
% 0.21/0.51          | ((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.21/0.51          | ~ (v1_relat_1 @ X1)
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ X0 @ 
% 0.21/0.51              (k4_tarski @ (sk_B_1 @ (k11_relat_1 @ X1 @ X0)) @ 
% 0.21/0.51               (sk_C_3 @ (k11_relat_1 @ X1 @ X0)))) @ 
% 0.21/0.51             X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (((r2_hidden @ 
% 0.21/0.51         (k4_tarski @ sk_A @ 
% 0.21/0.51          (k4_tarski @ (sk_B_1 @ (k11_relat_1 @ sk_B_2 @ sk_A)) @ 
% 0.21/0.51           (sk_C_3 @ (k11_relat_1 @ sk_B_2 @ sk_A)))) @ 
% 0.21/0.51         sk_B_2)
% 0.21/0.51        | ~ (v1_relat_1 @ sk_B_2)
% 0.21/0.51        | ((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['32', '35'])).
% 0.21/0.51  thf('37', plain, ((v1_relat_1 @ sk_B_2)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (((r2_hidden @ 
% 0.21/0.51         (k4_tarski @ sk_A @ 
% 0.21/0.51          (k4_tarski @ (sk_B_1 @ (k11_relat_1 @ sk_B_2 @ sk_A)) @ 
% 0.21/0.51           (sk_C_3 @ (k11_relat_1 @ sk_B_2 @ sk_A)))) @ 
% 0.21/0.51         sk_B_2)
% 0.21/0.51        | ((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      ((((k11_relat_1 @ sk_B_2 @ sk_A) != (k1_xboole_0)))
% 0.21/0.51         <= (~ (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.51      inference('split', [status(esa)], ['2'])).
% 0.21/0.51  thf('40', plain, (~ (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['3', '19'])).
% 0.21/0.51  thf('41', plain, (((k11_relat_1 @ sk_B_2 @ sk_A) != (k1_xboole_0))),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['39', '40'])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      ((r2_hidden @ 
% 0.21/0.51        (k4_tarski @ sk_A @ 
% 0.21/0.51         (k4_tarski @ (sk_B_1 @ (k11_relat_1 @ sk_B_2 @ sk_A)) @ 
% 0.21/0.51          (sk_C_3 @ (k11_relat_1 @ sk_B_2 @ sk_A)))) @ 
% 0.21/0.51        sk_B_2)),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['38', '41'])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.51         ((r2_hidden @ X11 @ (k1_relat_1 @ X13))
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X11 @ X12) @ X13))),
% 0.21/0.51      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.51  thf('44', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))),
% 0.21/0.51      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.52  thf('45', plain, ($false), inference('demod', [status(thm)], ['22', '44'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.36/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
