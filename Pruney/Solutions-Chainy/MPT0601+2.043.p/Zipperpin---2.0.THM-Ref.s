%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a9Gov17Tz6

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 133 expanded)
%              Number of leaves         :   21 (  46 expanded)
%              Depth                    :   17
%              Number of atoms          :  469 (1114 expanded)
%              Number of equality atoms :   25 (  69 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

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
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('5',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ( r2_hidden @ ( k4_tarski @ X13 @ ( sk_D_1 @ X13 @ X11 ) ) @ X11 )
      | ( X12
       != ( k1_relat_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('7',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X13 @ ( sk_D_1 @ X13 @ X11 ) ) @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ sk_B ) ) @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('9',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X25 @ X23 ) @ X24 )
      | ( r2_hidden @ X23 @ ( k11_relat_1 @ X24 @ X25 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('10',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k11_relat_1 @ sk_B @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k11_relat_1 @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
      & ( ( k11_relat_1 @ sk_B @ sk_A )
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
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['3','19','20'])).

thf('22',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['1','21'])).

thf('23',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14
        = ( k1_relat_1 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X14 @ X11 ) @ ( sk_D @ X14 @ X11 ) ) @ X11 )
      | ( r2_hidden @ ( sk_C_2 @ X14 @ X11 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 ) @ X1 )
      | ( X0
        = ( k1_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('29',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['3','19'])).

thf('30',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ ( k11_relat_1 @ sk_B @ sk_A ) ) @ ( k11_relat_1 @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('33',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ ( k11_relat_1 @ sk_B @ sk_A ) ) @ ( k11_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['31','34'])).

thf('36',plain,(
    r2_hidden @ ( sk_C_1 @ ( k11_relat_1 @ sk_B @ sk_A ) ) @ ( k11_relat_1 @ sk_B @ sk_A ) ),
    inference(condensation,[status(thm)],['35'])).

thf('37',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X23 @ ( k11_relat_1 @ X24 @ X25 ) )
      | ( r2_hidden @ ( k4_tarski @ X25 @ X23 ) @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C_1 @ ( k11_relat_1 @ sk_B @ sk_A ) ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C_1 @ ( k11_relat_1 @ sk_B @ sk_A ) ) ) @ sk_B ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X11 )
      | ( r2_hidden @ X9 @ X12 )
      | ( X12
       != ( k1_relat_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('42',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X9 @ ( k1_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X11 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['22','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a9Gov17Tz6
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:45:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 96 iterations in 0.077s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.21/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.21/0.54  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.21/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.54  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.21/0.54  thf(t205_relat_1, conjecture,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ B ) =>
% 0.21/0.54       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.21/0.54         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i,B:$i]:
% 0.21/0.54        ( ( v1_relat_1 @ B ) =>
% 0.21/0.54          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.21/0.54            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.21/0.54        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.21/0.54         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))
% 0.21/0.54        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.21/0.54       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.21/0.54      inference('split', [status(esa)], ['2'])).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.21/0.54         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.21/0.54         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.21/0.54      inference('split', [status(esa)], ['2'])).
% 0.21/0.54  thf(d4_relat_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.21/0.54       ( ![C:$i]:
% 0.21/0.54         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.54           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X13 @ X12)
% 0.21/0.54          | (r2_hidden @ (k4_tarski @ X13 @ (sk_D_1 @ X13 @ X11)) @ X11)
% 0.21/0.54          | ((X12) != (k1_relat_1 @ X11)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      (![X11 : $i, X13 : $i]:
% 0.21/0.54         ((r2_hidden @ (k4_tarski @ X13 @ (sk_D_1 @ X13 @ X11)) @ X11)
% 0.21/0.54          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X11)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ sk_B)) @ sk_B))
% 0.21/0.54         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['5', '7'])).
% 0.21/0.54  thf(t204_relat_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ C ) =>
% 0.21/0.54       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.21/0.54         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.54         (~ (r2_hidden @ (k4_tarski @ X25 @ X23) @ X24)
% 0.21/0.54          | (r2_hidden @ X23 @ (k11_relat_1 @ X24 @ X25))
% 0.21/0.54          | ~ (v1_relat_1 @ X24))),
% 0.21/0.54      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (((~ (v1_relat_1 @ sk_B)
% 0.21/0.54         | (r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k11_relat_1 @ sk_B @ sk_A))))
% 0.21/0.54         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.54  thf('11', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k11_relat_1 @ sk_B @ sk_A)))
% 0.21/0.54         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.21/0.54      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ k1_xboole_0))
% 0.21/0.54         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) & 
% 0.21/0.54             (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.21/0.54      inference('sup+', [status(thm)], ['4', '12'])).
% 0.21/0.54  thf(t2_boole, axiom,
% 0.21/0.54    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.54  thf(t4_xboole_0, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.54            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.21/0.54          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.54      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.54  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.54  thf('17', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.21/0.54      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.54  thf('18', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.21/0.54      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) | 
% 0.21/0.54       ~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['13', '18'])).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) | 
% 0.21/0.54       (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('21', plain, (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['3', '19', '20'])).
% 0.21/0.54  thf('22', plain, (~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['1', '21'])).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      (![X11 : $i, X14 : $i]:
% 0.21/0.54         (((X14) = (k1_relat_1 @ X11))
% 0.21/0.54          | (r2_hidden @ 
% 0.21/0.54             (k4_tarski @ (sk_C_2 @ X14 @ X11) @ (sk_D @ X14 @ X11)) @ X11)
% 0.21/0.54          | (r2_hidden @ (sk_C_2 @ X14 @ X11) @ X14))),
% 0.21/0.54      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.54  thf(t7_tarski, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ~( ( r2_hidden @ A @ B ) & 
% 0.21/0.54          ( ![C:$i]:
% 0.21/0.54            ( ~( ( r2_hidden @ C @ B ) & 
% 0.21/0.54                 ( ![D:$i]:
% 0.21/0.54                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (![X6 : $i, X7 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X6 @ X7) | (r2_hidden @ (sk_C_1 @ X7) @ X7))),
% 0.21/0.54      inference('cnf', [status(esa)], [t7_tarski])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((r2_hidden @ (sk_C_2 @ X1 @ X0) @ X1)
% 0.21/0.54          | ((X1) = (k1_relat_1 @ X0))
% 0.21/0.54          | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (![X6 : $i, X7 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X6 @ X7) | (r2_hidden @ (sk_C_1 @ X7) @ X7))),
% 0.21/0.54      inference('cnf', [status(esa)], [t7_tarski])).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((r2_hidden @ (sk_C_1 @ X1) @ X1)
% 0.21/0.54          | ((X0) = (k1_relat_1 @ X1))
% 0.21/0.54          | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.21/0.54         <= (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.21/0.54      inference('split', [status(esa)], ['2'])).
% 0.21/0.54  thf('29', plain, (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['3', '19'])).
% 0.21/0.54  thf('30', plain, (((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['28', '29'])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k1_relat_1 @ X0) != (k1_xboole_0))
% 0.21/0.54          | (r2_hidden @ (sk_C_1 @ (k11_relat_1 @ sk_B @ sk_A)) @ 
% 0.21/0.54             (k11_relat_1 @ sk_B @ sk_A))
% 0.21/0.54          | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['27', '30'])).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((r2_hidden @ (sk_C_2 @ X1 @ X0) @ X1)
% 0.21/0.54          | ((X1) = (k1_relat_1 @ X0))
% 0.21/0.54          | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.54  thf('33', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.21/0.54      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.54  thf('34', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((r2_hidden @ (sk_C_1 @ X0) @ X0)
% 0.21/0.54          | ((k1_xboole_0) = (k1_relat_1 @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((r2_hidden @ (sk_C_1 @ X0) @ X0)
% 0.21/0.54          | (r2_hidden @ (sk_C_1 @ (k11_relat_1 @ sk_B @ sk_A)) @ 
% 0.21/0.54             (k11_relat_1 @ sk_B @ sk_A)))),
% 0.21/0.54      inference('clc', [status(thm)], ['31', '34'])).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      ((r2_hidden @ (sk_C_1 @ (k11_relat_1 @ sk_B @ sk_A)) @ 
% 0.21/0.54        (k11_relat_1 @ sk_B @ sk_A))),
% 0.21/0.54      inference('condensation', [status(thm)], ['35'])).
% 0.21/0.54  thf('37', plain,
% 0.21/0.54      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X23 @ (k11_relat_1 @ X24 @ X25))
% 0.21/0.54          | (r2_hidden @ (k4_tarski @ X25 @ X23) @ X24)
% 0.21/0.54          | ~ (v1_relat_1 @ X24))),
% 0.21/0.54      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.21/0.54  thf('38', plain,
% 0.21/0.54      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.54        | (r2_hidden @ 
% 0.21/0.54           (k4_tarski @ sk_A @ (sk_C_1 @ (k11_relat_1 @ sk_B @ sk_A))) @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.54  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      ((r2_hidden @ 
% 0.21/0.54        (k4_tarski @ sk_A @ (sk_C_1 @ (k11_relat_1 @ sk_B @ sk_A))) @ sk_B)),
% 0.21/0.54      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.54         (~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ X11)
% 0.21/0.54          | (r2_hidden @ X9 @ X12)
% 0.21/0.54          | ((X12) != (k1_relat_1 @ X11)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.54         ((r2_hidden @ X9 @ (k1_relat_1 @ X11))
% 0.21/0.54          | ~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ X11))),
% 0.21/0.54      inference('simplify', [status(thm)], ['41'])).
% 0.21/0.54  thf('43', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['40', '42'])).
% 0.21/0.54  thf('44', plain, ($false), inference('demod', [status(thm)], ['22', '43'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
