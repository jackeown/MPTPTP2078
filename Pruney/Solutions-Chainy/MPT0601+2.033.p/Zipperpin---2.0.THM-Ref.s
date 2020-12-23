%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.l9hzMd9kp4

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:45 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 160 expanded)
%              Number of leaves         :   21 (  51 expanded)
%              Depth                    :   15
%              Number of atoms          :  492 (1411 expanded)
%              Number of equality atoms :   23 (  89 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ( r2_hidden @ ( k4_tarski @ X13 @ ( sk_D_2 @ X13 @ X11 ) ) @ X11 )
      | ( X12
       != ( k1_relat_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('7',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X13 @ ( sk_D_2 @ X13 @ X11 ) ) @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X11 ) ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X23 @ X21 ) @ X22 )
      | ( r2_hidden @ X21 @ ( k11_relat_1 @ X22 @ X23 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
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

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('15',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X2 ) @ X3 )
      | ~ ( r2_hidden @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('16',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) )
    | ( ( k11_relat_1 @ sk_B_2 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) )
    | ( ( k11_relat_1 @ sk_B_2 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference('sat_resolution*',[status(thm)],['3','17','18'])).

thf('20',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(simpl_trail,[status(thm)],['1','19'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('21',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ X6 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('22',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k11_relat_1 @ X22 @ X23 ) )
      | ( r2_hidden @ ( k4_tarski @ X23 @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k11_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_B @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X11 )
      | ( r2_hidden @ X9 @ X12 )
      | ( X12
       != ( k1_relat_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('25',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X9 @ ( k1_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X11 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k11_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,
    ( ( ( v1_relat_1 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B_2 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v1_relat_1 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference('sat_resolution*',[status(thm)],['3','17','18'])).

thf('32',plain,(
    v1_relat_1 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['30','31'])).

thf(t56_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf('33',plain,(
    ! [X24: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X24 ) @ ( sk_C_2 @ X24 ) ) @ X24 )
      | ( X24 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf('34',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k11_relat_1 @ X22 @ X23 ) )
      | ( r2_hidden @ ( k4_tarski @ X23 @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k11_relat_1 @ X1 @ X0 ) )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k4_tarski @ ( sk_B_1 @ ( k11_relat_1 @ X1 @ X0 ) ) @ ( sk_C_2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k4_tarski @ ( sk_B_1 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ) @ ( sk_C_2 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ) ) ) @ sk_B_2 )
    | ~ ( v1_relat_1 @ sk_B_2 )
    | ( ( k11_relat_1 @ sk_B_2 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k4_tarski @ ( sk_B_1 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ) @ ( sk_C_2 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ) ) ) @ sk_B_2 )
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
    inference('sat_resolution*',[status(thm)],['3','17'])).

thf('41',plain,(
    ( k11_relat_1 @ sk_B_2 @ sk_A )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['39','40'])).

thf('42',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k4_tarski @ ( sk_B_1 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ) @ ( sk_C_2 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ) ) ) @ sk_B_2 ),
    inference('simplify_reflect-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X9 @ ( k1_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X11 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('44',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['20','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.l9hzMd9kp4
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:58:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.37/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.59  % Solved by: fo/fo7.sh
% 0.37/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.59  % done 77 iterations in 0.085s
% 0.37/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.59  % SZS output start Refutation
% 0.37/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.59  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.37/0.59  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.37/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.59  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 0.37/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.59  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.37/0.59  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.59  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.37/0.59  thf(t205_relat_1, conjecture,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( v1_relat_1 @ B ) =>
% 0.37/0.59       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.37/0.59         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.37/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.59    (~( ![A:$i,B:$i]:
% 0.37/0.59        ( ( v1_relat_1 @ B ) =>
% 0.37/0.59          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.37/0.59            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.37/0.59    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.37/0.59  thf('0', plain,
% 0.37/0.59      ((((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))
% 0.37/0.59        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('1', plain,
% 0.37/0.59      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))
% 0.37/0.59         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.37/0.59      inference('split', [status(esa)], ['0'])).
% 0.37/0.59  thf('2', plain,
% 0.37/0.59      ((((k11_relat_1 @ sk_B_2 @ sk_A) != (k1_xboole_0))
% 0.37/0.59        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('3', plain,
% 0.37/0.59      (~ (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))) | 
% 0.37/0.59       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))),
% 0.37/0.59      inference('split', [status(esa)], ['2'])).
% 0.37/0.59  thf('4', plain,
% 0.37/0.59      ((((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0)))
% 0.37/0.59         <= ((((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))))),
% 0.37/0.59      inference('split', [status(esa)], ['0'])).
% 0.37/0.59  thf('5', plain,
% 0.37/0.59      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))
% 0.37/0.59         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.37/0.59      inference('split', [status(esa)], ['2'])).
% 0.37/0.59  thf(d4_relat_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.37/0.59       ( ![C:$i]:
% 0.37/0.59         ( ( r2_hidden @ C @ B ) <=>
% 0.37/0.59           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.37/0.59  thf('6', plain,
% 0.37/0.59      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.59         (~ (r2_hidden @ X13 @ X12)
% 0.37/0.59          | (r2_hidden @ (k4_tarski @ X13 @ (sk_D_2 @ X13 @ X11)) @ X11)
% 0.37/0.59          | ((X12) != (k1_relat_1 @ X11)))),
% 0.37/0.59      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.37/0.59  thf('7', plain,
% 0.37/0.59      (![X11 : $i, X13 : $i]:
% 0.37/0.59         ((r2_hidden @ (k4_tarski @ X13 @ (sk_D_2 @ X13 @ X11)) @ X11)
% 0.37/0.59          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X11)))),
% 0.37/0.59      inference('simplify', [status(thm)], ['6'])).
% 0.37/0.59  thf('8', plain,
% 0.37/0.59      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_2 @ sk_A @ sk_B_2)) @ sk_B_2))
% 0.37/0.59         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.37/0.59      inference('sup-', [status(thm)], ['5', '7'])).
% 0.37/0.59  thf(t204_relat_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( v1_relat_1 @ C ) =>
% 0.37/0.59       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.37/0.59         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.37/0.59  thf('9', plain,
% 0.37/0.59      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.37/0.59         (~ (r2_hidden @ (k4_tarski @ X23 @ X21) @ X22)
% 0.37/0.59          | (r2_hidden @ X21 @ (k11_relat_1 @ X22 @ X23))
% 0.37/0.59          | ~ (v1_relat_1 @ X22))),
% 0.37/0.59      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.37/0.59  thf('10', plain,
% 0.37/0.59      (((~ (v1_relat_1 @ sk_B_2)
% 0.37/0.59         | (r2_hidden @ (sk_D_2 @ sk_A @ sk_B_2) @ 
% 0.37/0.59            (k11_relat_1 @ sk_B_2 @ sk_A))))
% 0.37/0.59         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.37/0.59      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.59  thf('11', plain, ((v1_relat_1 @ sk_B_2)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('12', plain,
% 0.37/0.59      (((r2_hidden @ (sk_D_2 @ sk_A @ sk_B_2) @ (k11_relat_1 @ sk_B_2 @ sk_A)))
% 0.37/0.59         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.37/0.59      inference('demod', [status(thm)], ['10', '11'])).
% 0.37/0.59  thf('13', plain,
% 0.37/0.59      (((r2_hidden @ (sk_D_2 @ sk_A @ sk_B_2) @ k1_xboole_0))
% 0.37/0.59         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))) & 
% 0.37/0.59             (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))))),
% 0.37/0.59      inference('sup+', [status(thm)], ['4', '12'])).
% 0.37/0.59  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.37/0.59  thf('14', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.37/0.59      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.37/0.59  thf(t55_zfmisc_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.37/0.59  thf('15', plain,
% 0.37/0.59      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.59         (~ (r1_xboole_0 @ (k2_tarski @ X1 @ X2) @ X3)
% 0.37/0.59          | ~ (r2_hidden @ X1 @ X3))),
% 0.37/0.59      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.37/0.59  thf('16', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.37/0.59      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.59  thf('17', plain,
% 0.37/0.59      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))) | 
% 0.37/0.59       ~ (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['13', '16'])).
% 0.37/0.59  thf('18', plain,
% 0.37/0.59      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))) | 
% 0.37/0.59       (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0)))),
% 0.37/0.59      inference('split', [status(esa)], ['0'])).
% 0.37/0.59  thf('19', plain, (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))),
% 0.37/0.59      inference('sat_resolution*', [status(thm)], ['3', '17', '18'])).
% 0.37/0.59  thf('20', plain, (~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))),
% 0.37/0.59      inference('simpl_trail', [status(thm)], ['1', '19'])).
% 0.37/0.59  thf(d1_relat_1, axiom,
% 0.37/0.59    (![A:$i]:
% 0.37/0.59     ( ( v1_relat_1 @ A ) <=>
% 0.37/0.59       ( ![B:$i]:
% 0.37/0.59         ( ~( ( r2_hidden @ B @ A ) & 
% 0.37/0.59              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.37/0.59  thf('21', plain,
% 0.37/0.59      (![X6 : $i]: ((v1_relat_1 @ X6) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.37/0.59      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.37/0.59  thf('22', plain,
% 0.37/0.59      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.37/0.59         (~ (r2_hidden @ X21 @ (k11_relat_1 @ X22 @ X23))
% 0.37/0.59          | (r2_hidden @ (k4_tarski @ X23 @ X21) @ X22)
% 0.37/0.59          | ~ (v1_relat_1 @ X22))),
% 0.37/0.59      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.37/0.59  thf('23', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((v1_relat_1 @ (k11_relat_1 @ X1 @ X0))
% 0.37/0.59          | ~ (v1_relat_1 @ X1)
% 0.37/0.59          | (r2_hidden @ (k4_tarski @ X0 @ (sk_B @ (k11_relat_1 @ X1 @ X0))) @ 
% 0.37/0.59             X1))),
% 0.37/0.59      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.59  thf('24', plain,
% 0.37/0.59      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.59         (~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ X11)
% 0.37/0.59          | (r2_hidden @ X9 @ X12)
% 0.37/0.59          | ((X12) != (k1_relat_1 @ X11)))),
% 0.37/0.59      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.37/0.59  thf('25', plain,
% 0.37/0.59      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.37/0.59         ((r2_hidden @ X9 @ (k1_relat_1 @ X11))
% 0.37/0.59          | ~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ X11))),
% 0.37/0.59      inference('simplify', [status(thm)], ['24'])).
% 0.37/0.59  thf('26', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         (~ (v1_relat_1 @ X0)
% 0.37/0.59          | (v1_relat_1 @ (k11_relat_1 @ X0 @ X1))
% 0.37/0.59          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['23', '25'])).
% 0.37/0.59  thf('27', plain,
% 0.37/0.59      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))
% 0.37/0.59         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.37/0.59      inference('split', [status(esa)], ['0'])).
% 0.37/0.59  thf('28', plain,
% 0.37/0.59      ((((v1_relat_1 @ (k11_relat_1 @ sk_B_2 @ sk_A)) | ~ (v1_relat_1 @ sk_B_2)))
% 0.37/0.59         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.37/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.37/0.59  thf('29', plain, ((v1_relat_1 @ sk_B_2)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('30', plain,
% 0.37/0.59      (((v1_relat_1 @ (k11_relat_1 @ sk_B_2 @ sk_A)))
% 0.37/0.59         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.37/0.59      inference('demod', [status(thm)], ['28', '29'])).
% 0.37/0.59  thf('31', plain, (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))),
% 0.37/0.59      inference('sat_resolution*', [status(thm)], ['3', '17', '18'])).
% 0.37/0.59  thf('32', plain, ((v1_relat_1 @ (k11_relat_1 @ sk_B_2 @ sk_A))),
% 0.37/0.59      inference('simpl_trail', [status(thm)], ['30', '31'])).
% 0.37/0.59  thf(t56_relat_1, axiom,
% 0.37/0.59    (![A:$i]:
% 0.37/0.59     ( ( v1_relat_1 @ A ) =>
% 0.37/0.59       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.37/0.59         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.37/0.59  thf('33', plain,
% 0.37/0.59      (![X24 : $i]:
% 0.37/0.59         ((r2_hidden @ (k4_tarski @ (sk_B_1 @ X24) @ (sk_C_2 @ X24)) @ X24)
% 0.37/0.59          | ((X24) = (k1_xboole_0))
% 0.37/0.59          | ~ (v1_relat_1 @ X24))),
% 0.37/0.59      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.37/0.59  thf('34', plain,
% 0.37/0.59      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.37/0.59         (~ (r2_hidden @ X21 @ (k11_relat_1 @ X22 @ X23))
% 0.37/0.59          | (r2_hidden @ (k4_tarski @ X23 @ X21) @ X22)
% 0.37/0.59          | ~ (v1_relat_1 @ X22))),
% 0.37/0.59      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.37/0.59  thf('35', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         (~ (v1_relat_1 @ (k11_relat_1 @ X1 @ X0))
% 0.37/0.59          | ((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.37/0.59          | ~ (v1_relat_1 @ X1)
% 0.37/0.59          | (r2_hidden @ 
% 0.37/0.59             (k4_tarski @ X0 @ 
% 0.37/0.59              (k4_tarski @ (sk_B_1 @ (k11_relat_1 @ X1 @ X0)) @ 
% 0.37/0.59               (sk_C_2 @ (k11_relat_1 @ X1 @ X0)))) @ 
% 0.37/0.59             X1))),
% 0.37/0.59      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.59  thf('36', plain,
% 0.37/0.59      (((r2_hidden @ 
% 0.37/0.59         (k4_tarski @ sk_A @ 
% 0.37/0.59          (k4_tarski @ (sk_B_1 @ (k11_relat_1 @ sk_B_2 @ sk_A)) @ 
% 0.37/0.59           (sk_C_2 @ (k11_relat_1 @ sk_B_2 @ sk_A)))) @ 
% 0.37/0.59         sk_B_2)
% 0.37/0.59        | ~ (v1_relat_1 @ sk_B_2)
% 0.37/0.59        | ((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['32', '35'])).
% 0.37/0.59  thf('37', plain, ((v1_relat_1 @ sk_B_2)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('38', plain,
% 0.37/0.59      (((r2_hidden @ 
% 0.37/0.59         (k4_tarski @ sk_A @ 
% 0.37/0.59          (k4_tarski @ (sk_B_1 @ (k11_relat_1 @ sk_B_2 @ sk_A)) @ 
% 0.37/0.59           (sk_C_2 @ (k11_relat_1 @ sk_B_2 @ sk_A)))) @ 
% 0.37/0.59         sk_B_2)
% 0.37/0.59        | ((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0)))),
% 0.37/0.59      inference('demod', [status(thm)], ['36', '37'])).
% 0.37/0.59  thf('39', plain,
% 0.37/0.59      ((((k11_relat_1 @ sk_B_2 @ sk_A) != (k1_xboole_0)))
% 0.37/0.59         <= (~ (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))))),
% 0.37/0.59      inference('split', [status(esa)], ['2'])).
% 0.37/0.59  thf('40', plain, (~ (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0)))),
% 0.37/0.59      inference('sat_resolution*', [status(thm)], ['3', '17'])).
% 0.37/0.59  thf('41', plain, (((k11_relat_1 @ sk_B_2 @ sk_A) != (k1_xboole_0))),
% 0.37/0.59      inference('simpl_trail', [status(thm)], ['39', '40'])).
% 0.37/0.59  thf('42', plain,
% 0.37/0.59      ((r2_hidden @ 
% 0.37/0.59        (k4_tarski @ sk_A @ 
% 0.37/0.59         (k4_tarski @ (sk_B_1 @ (k11_relat_1 @ sk_B_2 @ sk_A)) @ 
% 0.37/0.59          (sk_C_2 @ (k11_relat_1 @ sk_B_2 @ sk_A)))) @ 
% 0.37/0.59        sk_B_2)),
% 0.37/0.59      inference('simplify_reflect-', [status(thm)], ['38', '41'])).
% 0.37/0.59  thf('43', plain,
% 0.37/0.59      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.37/0.59         ((r2_hidden @ X9 @ (k1_relat_1 @ X11))
% 0.37/0.59          | ~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ X11))),
% 0.37/0.59      inference('simplify', [status(thm)], ['24'])).
% 0.37/0.59  thf('44', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))),
% 0.37/0.59      inference('sup-', [status(thm)], ['42', '43'])).
% 0.37/0.59  thf('45', plain, ($false), inference('demod', [status(thm)], ['20', '44'])).
% 0.37/0.59  
% 0.37/0.59  % SZS output end Refutation
% 0.37/0.59  
% 0.37/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
