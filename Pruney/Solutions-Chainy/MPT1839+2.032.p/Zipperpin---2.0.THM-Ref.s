%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zJRp2tzZkT

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:26 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 391 expanded)
%              Number of leaves         :   22 ( 123 expanded)
%              Depth                    :   17
%              Number of atoms          :  496 (3031 expanded)
%              Number of equality atoms :   52 ( 187 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('0',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( v1_zfmisc_1 @ X26 )
      | ( X27 = X26 )
      | ~ ( r1_tarski @ X27 @ X26 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t2_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) )
         => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v1_xboole_0 @ A )
          & ( v1_zfmisc_1 @ A ) )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) )
           => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t2_tex_2])).

thf('3',plain,(
    ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( ( k3_xboole_0 @ sk_A @ sk_B_2 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k3_xboole_0 @ sk_A @ sk_B_2 )
      = sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_2 )
    = sk_A ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_2 )
    = sk_A ),
    inference(clc,[status(thm)],['6','7'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r1_xboole_0 @ X15 @ X17 )
      | ( ( k4_xboole_0 @ X15 @ X17 )
       != X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('13',plain,
    ( ( ( k5_xboole_0 @ sk_A @ sk_A )
     != sk_A )
    | ( r1_xboole_0 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('16',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( v1_zfmisc_1 @ X26 )
      | ( X27 = X26 )
      | ~ ( r1_tarski @ X27 @ X26 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( ( k4_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
      = sk_A ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k5_xboole_0 @ sk_A @ sk_A )
      = sk_A ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_A ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_2 )
    = sk_A ),
    inference(clc,[status(thm)],['6','7'])).

thf(t1_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X25: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X25 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t1_mcart_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('32',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r1_xboole_0 @ X15 @ X17 )
      | ( ( k4_xboole_0 @ X15 @ X17 )
       != X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','38'])).

thf('40',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ sk_A )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','41'])).

thf('43',plain,
    ( ( k1_xboole_0
      = ( k5_xboole_0 @ sk_A @ sk_A ) )
    | ~ ( v1_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','42'])).

thf('44',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('45',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( ( k4_xboole_0 @ X6 @ X7 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('46',plain,
    ( ( ( k5_xboole_0 @ sk_A @ sk_A )
     != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ( k5_xboole_0 @ sk_A @ sk_A )
 != k1_xboole_0 ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['43','48'])).

thf('50',plain,
    ( ( ( k5_xboole_0 @ sk_A @ sk_A )
      = sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['21','49'])).

thf('51',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k5_xboole_0 @ sk_A @ sk_A )
    = sk_A ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_A != sk_A )
    | ( r1_xboole_0 @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['13','52'])).

thf('54',plain,(
    r1_xboole_0 @ sk_A @ sk_B_2 ),
    inference(simplify,[status(thm)],['53'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('55',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('56',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup+',[status(thm)],['8','56'])).

thf('58',plain,(
    ( k5_xboole_0 @ sk_A @ sk_A )
 != k1_xboole_0 ),
    inference(clc,[status(thm)],['46','47'])).

thf('59',plain,
    ( ( k5_xboole_0 @ sk_A @ sk_A )
    = sk_A ),
    inference(clc,[status(thm)],['50','51'])).

thf('60',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['57','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zJRp2tzZkT
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:14:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.59/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.77  % Solved by: fo/fo7.sh
% 0.59/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.77  % done 1013 iterations in 0.319s
% 0.59/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.77  % SZS output start Refutation
% 0.59/0.77  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.59/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.77  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.59/0.77  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.59/0.77  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.59/0.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.77  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.59/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.77  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.59/0.77  thf(t17_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.59/0.77  thf('0', plain,
% 0.59/0.77      (![X11 : $i, X12 : $i]: (r1_tarski @ (k3_xboole_0 @ X11 @ X12) @ X11)),
% 0.59/0.77      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.59/0.77  thf(t1_tex_2, axiom,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.59/0.77       ( ![B:$i]:
% 0.59/0.77         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.59/0.77           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.59/0.77  thf('1', plain,
% 0.59/0.77      (![X26 : $i, X27 : $i]:
% 0.59/0.77         ((v1_xboole_0 @ X26)
% 0.59/0.77          | ~ (v1_zfmisc_1 @ X26)
% 0.59/0.77          | ((X27) = (X26))
% 0.59/0.77          | ~ (r1_tarski @ X27 @ X26)
% 0.59/0.77          | (v1_xboole_0 @ X27))),
% 0.59/0.77      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.59/0.77  thf('2', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((v1_xboole_0 @ (k3_xboole_0 @ X0 @ X1))
% 0.59/0.77          | ((k3_xboole_0 @ X0 @ X1) = (X0))
% 0.59/0.77          | ~ (v1_zfmisc_1 @ X0)
% 0.59/0.77          | (v1_xboole_0 @ X0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['0', '1'])).
% 0.59/0.77  thf(t2_tex_2, conjecture,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.59/0.77       ( ![B:$i]:
% 0.59/0.77         ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 0.59/0.77           ( r1_tarski @ A @ B ) ) ) ))).
% 0.59/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.77    (~( ![A:$i]:
% 0.59/0.77        ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.59/0.77          ( ![B:$i]:
% 0.59/0.77            ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 0.59/0.77              ( r1_tarski @ A @ B ) ) ) ) )),
% 0.59/0.77    inference('cnf.neg', [status(esa)], [t2_tex_2])).
% 0.59/0.77  thf('3', plain, (~ (v1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_2))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('4', plain,
% 0.59/0.77      (((v1_xboole_0 @ sk_A)
% 0.59/0.77        | ~ (v1_zfmisc_1 @ sk_A)
% 0.59/0.77        | ((k3_xboole_0 @ sk_A @ sk_B_2) = (sk_A)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['2', '3'])).
% 0.59/0.77  thf('5', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('6', plain,
% 0.59/0.77      (((v1_xboole_0 @ sk_A) | ((k3_xboole_0 @ sk_A @ sk_B_2) = (sk_A)))),
% 0.59/0.77      inference('demod', [status(thm)], ['4', '5'])).
% 0.59/0.77  thf('7', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('8', plain, (((k3_xboole_0 @ sk_A @ sk_B_2) = (sk_A))),
% 0.59/0.77      inference('clc', [status(thm)], ['6', '7'])).
% 0.59/0.77  thf('9', plain, (((k3_xboole_0 @ sk_A @ sk_B_2) = (sk_A))),
% 0.59/0.77      inference('clc', [status(thm)], ['6', '7'])).
% 0.59/0.77  thf(t100_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.59/0.77  thf('10', plain,
% 0.59/0.77      (![X9 : $i, X10 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ X9 @ X10)
% 0.59/0.77           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.59/0.77  thf('11', plain,
% 0.59/0.77      (((k4_xboole_0 @ sk_A @ sk_B_2) = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.59/0.77      inference('sup+', [status(thm)], ['9', '10'])).
% 0.59/0.77  thf(t83_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.59/0.77  thf('12', plain,
% 0.59/0.77      (![X15 : $i, X17 : $i]:
% 0.59/0.77         ((r1_xboole_0 @ X15 @ X17) | ((k4_xboole_0 @ X15 @ X17) != (X15)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.59/0.77  thf('13', plain,
% 0.59/0.77      ((((k5_xboole_0 @ sk_A @ sk_A) != (sk_A)) | (r1_xboole_0 @ sk_A @ sk_B_2))),
% 0.59/0.77      inference('sup-', [status(thm)], ['11', '12'])).
% 0.59/0.77  thf('14', plain,
% 0.59/0.77      (((k4_xboole_0 @ sk_A @ sk_B_2) = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.59/0.77      inference('sup+', [status(thm)], ['9', '10'])).
% 0.59/0.77  thf(t36_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.59/0.77  thf('15', plain,
% 0.59/0.77      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.59/0.77      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.59/0.77  thf('16', plain,
% 0.59/0.77      (![X26 : $i, X27 : $i]:
% 0.59/0.77         ((v1_xboole_0 @ X26)
% 0.59/0.77          | ~ (v1_zfmisc_1 @ X26)
% 0.59/0.77          | ((X27) = (X26))
% 0.59/0.77          | ~ (r1_tarski @ X27 @ X26)
% 0.59/0.77          | (v1_xboole_0 @ X27))),
% 0.59/0.77      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.59/0.77  thf('17', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((v1_xboole_0 @ (k4_xboole_0 @ X0 @ X1))
% 0.59/0.77          | ((k4_xboole_0 @ X0 @ X1) = (X0))
% 0.59/0.77          | ~ (v1_zfmisc_1 @ X0)
% 0.59/0.77          | (v1_xboole_0 @ X0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['15', '16'])).
% 0.59/0.77  thf('18', plain,
% 0.59/0.77      (((v1_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_A))
% 0.59/0.77        | (v1_xboole_0 @ sk_A)
% 0.59/0.77        | ~ (v1_zfmisc_1 @ sk_A)
% 0.59/0.77        | ((k4_xboole_0 @ sk_A @ sk_B_2) = (sk_A)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['14', '17'])).
% 0.59/0.77  thf('19', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('20', plain,
% 0.59/0.77      (((k4_xboole_0 @ sk_A @ sk_B_2) = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.59/0.77      inference('sup+', [status(thm)], ['9', '10'])).
% 0.59/0.77  thf('21', plain,
% 0.59/0.77      (((v1_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_A))
% 0.59/0.77        | (v1_xboole_0 @ sk_A)
% 0.59/0.77        | ((k5_xboole_0 @ sk_A @ sk_A) = (sk_A)))),
% 0.59/0.77      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.59/0.77  thf('22', plain,
% 0.59/0.77      (((k4_xboole_0 @ sk_A @ sk_B_2) = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.59/0.77      inference('sup+', [status(thm)], ['9', '10'])).
% 0.59/0.77  thf('23', plain,
% 0.59/0.77      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.59/0.77      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.59/0.77  thf(l32_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.59/0.77  thf('24', plain,
% 0.59/0.77      (![X6 : $i, X8 : $i]:
% 0.59/0.77         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.59/0.77      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.59/0.77  thf('25', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['23', '24'])).
% 0.59/0.77  thf('26', plain,
% 0.59/0.77      (((k4_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_A) @ sk_A) = (k1_xboole_0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['22', '25'])).
% 0.59/0.77  thf('27', plain, (((k3_xboole_0 @ sk_A @ sk_B_2) = (sk_A))),
% 0.59/0.77      inference('clc', [status(thm)], ['6', '7'])).
% 0.59/0.77  thf(t1_mcart_1, axiom,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.59/0.77          ( ![B:$i]: ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ))).
% 0.59/0.77  thf('28', plain,
% 0.59/0.77      (![X25 : $i]:
% 0.59/0.77         (((X25) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X25) @ X25))),
% 0.59/0.77      inference('cnf', [status(esa)], [t1_mcart_1])).
% 0.59/0.77  thf(d1_xboole_0, axiom,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.59/0.77  thf('29', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.59/0.77      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.59/0.77  thf('30', plain,
% 0.59/0.77      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['28', '29'])).
% 0.59/0.77  thf('31', plain,
% 0.59/0.77      (![X11 : $i, X12 : $i]: (r1_tarski @ (k3_xboole_0 @ X11 @ X12) @ X11)),
% 0.59/0.77      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.59/0.77  thf('32', plain,
% 0.59/0.77      (![X6 : $i, X8 : $i]:
% 0.59/0.77         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.59/0.77      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.59/0.77  thf('33', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['31', '32'])).
% 0.59/0.77  thf('34', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['23', '24'])).
% 0.59/0.77  thf('35', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['33', '34'])).
% 0.59/0.77  thf('36', plain,
% 0.59/0.77      (![X15 : $i, X17 : $i]:
% 0.59/0.77         ((r1_xboole_0 @ X15 @ X17) | ((k4_xboole_0 @ X15 @ X17) != (X15)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.59/0.77  thf('37', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.77          | (r1_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['35', '36'])).
% 0.59/0.77  thf('38', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (r1_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))),
% 0.59/0.77      inference('simplify', [status(thm)], ['37'])).
% 0.59/0.77  thf('39', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         ((r1_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['30', '38'])).
% 0.59/0.77  thf('40', plain,
% 0.59/0.77      (![X15 : $i, X16 : $i]:
% 0.59/0.77         (((k4_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_xboole_0 @ X15 @ X16))),
% 0.59/0.77      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.59/0.77  thf('41', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (~ (v1_xboole_0 @ X2)
% 0.59/0.77          | ((k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) = (X2)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['39', '40'])).
% 0.59/0.77  thf('42', plain,
% 0.59/0.77      (![X0 : $i]: (((k4_xboole_0 @ X0 @ sk_A) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['27', '41'])).
% 0.59/0.77  thf('43', plain,
% 0.59/0.77      ((((k1_xboole_0) = (k5_xboole_0 @ sk_A @ sk_A))
% 0.59/0.77        | ~ (v1_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_A)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['26', '42'])).
% 0.59/0.77  thf('44', plain,
% 0.59/0.77      (((k4_xboole_0 @ sk_A @ sk_B_2) = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.59/0.77      inference('sup+', [status(thm)], ['9', '10'])).
% 0.59/0.77  thf('45', plain,
% 0.59/0.77      (![X6 : $i, X7 : $i]:
% 0.59/0.77         ((r1_tarski @ X6 @ X7) | ((k4_xboole_0 @ X6 @ X7) != (k1_xboole_0)))),
% 0.59/0.77      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.59/0.77  thf('46', plain,
% 0.59/0.77      ((((k5_xboole_0 @ sk_A @ sk_A) != (k1_xboole_0))
% 0.59/0.77        | (r1_tarski @ sk_A @ sk_B_2))),
% 0.59/0.77      inference('sup-', [status(thm)], ['44', '45'])).
% 0.59/0.77  thf('47', plain, (~ (r1_tarski @ sk_A @ sk_B_2)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('48', plain, (((k5_xboole_0 @ sk_A @ sk_A) != (k1_xboole_0))),
% 0.59/0.77      inference('clc', [status(thm)], ['46', '47'])).
% 0.59/0.77  thf('49', plain, (~ (v1_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_A))),
% 0.59/0.77      inference('simplify_reflect-', [status(thm)], ['43', '48'])).
% 0.59/0.77  thf('50', plain,
% 0.59/0.77      ((((k5_xboole_0 @ sk_A @ sk_A) = (sk_A)) | (v1_xboole_0 @ sk_A))),
% 0.59/0.77      inference('clc', [status(thm)], ['21', '49'])).
% 0.59/0.77  thf('51', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('52', plain, (((k5_xboole_0 @ sk_A @ sk_A) = (sk_A))),
% 0.59/0.77      inference('clc', [status(thm)], ['50', '51'])).
% 0.59/0.77  thf('53', plain, ((((sk_A) != (sk_A)) | (r1_xboole_0 @ sk_A @ sk_B_2))),
% 0.59/0.77      inference('demod', [status(thm)], ['13', '52'])).
% 0.59/0.77  thf('54', plain, ((r1_xboole_0 @ sk_A @ sk_B_2)),
% 0.59/0.77      inference('simplify', [status(thm)], ['53'])).
% 0.59/0.77  thf(d7_xboole_0, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.59/0.77       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.59/0.77  thf('55', plain,
% 0.59/0.77      (![X3 : $i, X4 : $i]:
% 0.59/0.77         (((k3_xboole_0 @ X3 @ X4) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X3 @ X4))),
% 0.59/0.77      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.59/0.77  thf('56', plain, (((k3_xboole_0 @ sk_A @ sk_B_2) = (k1_xboole_0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['54', '55'])).
% 0.59/0.77  thf('57', plain, (((sk_A) = (k1_xboole_0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['8', '56'])).
% 0.59/0.77  thf('58', plain, (((k5_xboole_0 @ sk_A @ sk_A) != (k1_xboole_0))),
% 0.59/0.77      inference('clc', [status(thm)], ['46', '47'])).
% 0.59/0.77  thf('59', plain, (((k5_xboole_0 @ sk_A @ sk_A) = (sk_A))),
% 0.59/0.77      inference('clc', [status(thm)], ['50', '51'])).
% 0.59/0.77  thf('60', plain, (((sk_A) != (k1_xboole_0))),
% 0.59/0.77      inference('demod', [status(thm)], ['58', '59'])).
% 0.59/0.77  thf('61', plain, ($false),
% 0.59/0.77      inference('simplify_reflect-', [status(thm)], ['57', '60'])).
% 0.59/0.77  
% 0.59/0.77  % SZS output end Refutation
% 0.59/0.77  
% 0.59/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
