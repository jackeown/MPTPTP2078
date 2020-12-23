%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UW9CZ4idrr

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 140 expanded)
%              Number of leaves         :   24 (  55 expanded)
%              Depth                    :   18
%              Number of atoms          :  464 (1325 expanded)
%              Number of equality atoms :   66 ( 187 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(np__1_type,type,(
    np__1: $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_3_type,type,(
    sk_B_3: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(spc1_boole,axiom,(
    ~ ( v1_xboole_0 @ np__1 ) )).

thf('0',plain,(
    ~ ( v1_xboole_0 @ np__1 ) ),
    inference(cnf,[status(esa)],[spc1_boole])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('1',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('2',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('4',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['1','4'])).

thf(t56_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf('6',plain,(
    ! [X6: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X6 ) @ ( sk_C_1 @ X6 ) ) @ X6 )
      | ( X6 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf(s3_funct_1__e2_25__funct_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ B @ C )
            = k1_xboole_0 ) )
      & ( ( k1_relat_1 @ B )
        = A )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k1_funct_1 @ ( sk_B_2 @ X7 ) @ X8 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( sk_B_2 @ X0 ) @ ( k4_tarski @ ( sk_B_1 @ X0 ) @ ( sk_C_1 @ X0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('9',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ X3 )
      | ( r2_hidden @ ( sk_B @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k1_funct_1 @ ( sk_B_2 @ X7 ) @ X8 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ X0 )
      | ( ( k1_funct_1 @ ( sk_B_2 @ X0 ) @ ( sk_B @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(s3_funct_1__e7_25__funct_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ B @ C )
            = np__1 ) )
      & ( ( k1_relat_1 @ B )
        = A )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('12',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( sk_B_3 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('13',plain,(
    ! [X7: $i] :
      ( ( k1_relat_1 @ ( sk_B_2 @ X7 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(t16_funct_1,conjecture,(
    ! [A: $i] :
      ( ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ( ( ( ( k1_relat_1 @ B )
                    = A )
                  & ( ( k1_relat_1 @ C )
                    = A ) )
               => ( B = C ) ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ! [C: $i] :
                ( ( ( v1_relat_1 @ C )
                  & ( v1_funct_1 @ C ) )
               => ( ( ( ( k1_relat_1 @ B )
                      = A )
                    & ( ( k1_relat_1 @ C )
                      = A ) )
                 => ( B = C ) ) ) )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t16_funct_1])).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X12 = X11 )
      | ( ( k1_relat_1 @ X11 )
       != sk_A_1 )
      | ( ( k1_relat_1 @ X12 )
       != sk_A_1 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A_1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A_1 )
      | ( X1
        = ( sk_B_2 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_B_2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_B_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X7: $i] :
      ( v1_funct_1 @ ( sk_B_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('17',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( sk_B_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A_1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A_1 )
      | ( X1
        = ( sk_B_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( sk_B_2 @ sk_A_1 ) )
      | ( ( k1_relat_1 @ X1 )
       != sk_A_1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_A_1 )
      | ~ ( v1_relat_1 @ ( sk_B_3 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_B_3 @ X0 ) )
      | ( ( sk_B_3 @ X0 )
        = ( sk_B_2 @ sk_A_1 ) ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( sk_B_3 @ X9 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('22',plain,(
    ! [X9: $i] :
      ( v1_funct_1 @ ( sk_B_3 @ X9 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_A_1 )
      | ( ( sk_B_3 @ X0 )
        = ( sk_B_2 @ sk_A_1 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( sk_B_3 @ sk_A_1 )
    = ( sk_B_2 @ sk_A_1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ X3 )
      | ( r2_hidden @ ( sk_B @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('26',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k1_funct_1 @ ( sk_B_3 @ X9 ) @ X10 )
        = np__1 )
      | ~ ( r2_hidden @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ X0 )
      | ( ( k1_funct_1 @ ( sk_B_3 @ X0 ) @ ( sk_B @ X0 ) )
        = np__1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k1_funct_1 @ ( sk_B_2 @ sk_A_1 ) @ ( sk_B @ sk_A_1 ) )
      = np__1 )
    | ( v1_relat_1 @ sk_A_1 ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,
    ( ( k1_xboole_0 = np__1 )
    | ( v1_relat_1 @ sk_A_1 )
    | ( v1_relat_1 @ sk_A_1 ) ),
    inference('sup+',[status(thm)],['11','28'])).

thf('30',plain,
    ( ( v1_relat_1 @ sk_A_1 )
    | ( k1_xboole_0 = np__1 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( sk_B_3 @ sk_A_1 )
    = ( sk_B_2 @ sk_A_1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('32',plain,(
    ! [X6: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X6 ) @ ( sk_C_1 @ X6 ) ) @ X6 )
      | ( X6 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf('33',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k1_funct_1 @ ( sk_B_3 @ X9 ) @ X10 )
        = np__1 )
      | ~ ( r2_hidden @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( sk_B_3 @ X0 ) @ ( k4_tarski @ ( sk_B_1 @ X0 ) @ ( sk_C_1 @ X0 ) ) )
        = np__1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k1_funct_1 @ ( sk_B_2 @ sk_A_1 ) @ ( k4_tarski @ ( sk_B_1 @ sk_A_1 ) @ ( sk_C_1 @ sk_A_1 ) ) )
      = np__1 )
    | ( sk_A_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A_1 ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k1_funct_1 @ ( sk_B_2 @ sk_A_1 ) @ ( k4_tarski @ ( sk_B_1 @ sk_A_1 ) @ ( sk_C_1 @ sk_A_1 ) ) )
      = np__1 )
    | ~ ( v1_relat_1 @ sk_A_1 ) ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k1_xboole_0 = np__1 )
    | ( ( k1_funct_1 @ ( sk_B_2 @ sk_A_1 ) @ ( k4_tarski @ ( sk_B_1 @ sk_A_1 ) @ ( sk_C_1 @ sk_A_1 ) ) )
      = np__1 ) ),
    inference('sup-',[status(thm)],['30','37'])).

thf('39',plain,
    ( ( k1_xboole_0 = np__1 )
    | ( sk_A_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A_1 )
    | ( k1_xboole_0 = np__1 ) ),
    inference('sup+',[status(thm)],['8','38'])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_A_1 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( k1_xboole_0 = np__1 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ sk_A_1 )
    | ( k1_xboole_0 = np__1 ) ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( v1_relat_1 @ sk_A_1 )
    | ( k1_xboole_0 = np__1 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('44',plain,(
    k1_xboole_0 = np__1 ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    v1_xboole_0 @ np__1 ),
    inference(demod,[status(thm)],['5','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['0','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UW9CZ4idrr
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:38:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 59 iterations in 0.038s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(np__1_type, type, np__1: $i).
% 0.20/0.49  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.49  thf(sk_B_3_type, type, sk_B_3: $i > $i).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.20/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.49  thf(sk_B_2_type, type, sk_B_2: $i > $i).
% 0.20/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.20/0.49  thf(spc1_boole, axiom, (~( v1_xboole_0 @ np__1 ))).
% 0.20/0.49  thf('0', plain, (~ (v1_xboole_0 @ np__1)),
% 0.20/0.49      inference('cnf', [status(esa)], [spc1_boole])).
% 0.20/0.49  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.20/0.49  thf('1', plain, ((v1_xboole_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.20/0.49  thf('2', plain, ((v1_xboole_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.20/0.49  thf(l13_xboole_0, axiom,
% 0.20/0.49    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.49  thf('4', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf('5', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.49      inference('demod', [status(thm)], ['1', '4'])).
% 0.20/0.49  thf(t56_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.20/0.49         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X6 : $i]:
% 0.20/0.49         ((r2_hidden @ (k4_tarski @ (sk_B_1 @ X6) @ (sk_C_1 @ X6)) @ X6)
% 0.20/0.49          | ((X6) = (k1_xboole_0))
% 0.20/0.49          | ~ (v1_relat_1 @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.20/0.49  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ?[B:$i]:
% 0.20/0.49       ( ( ![C:$i]:
% 0.20/0.49           ( ( r2_hidden @ C @ A ) =>
% 0.20/0.49             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.49         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.20/0.49         ( v1_relat_1 @ B ) ) ))).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i]:
% 0.20/0.49         (((k1_funct_1 @ (sk_B_2 @ X7) @ X8) = (k1_xboole_0))
% 0.20/0.49          | ~ (r2_hidden @ X8 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X0)
% 0.20/0.49          | ((X0) = (k1_xboole_0))
% 0.20/0.49          | ((k1_funct_1 @ (sk_B_2 @ X0) @ 
% 0.20/0.49              (k4_tarski @ (sk_B_1 @ X0) @ (sk_C_1 @ X0))) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf(d1_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) <=>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ~( ( r2_hidden @ B @ A ) & 
% 0.20/0.49              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X3 : $i]: ((v1_relat_1 @ X3) | (r2_hidden @ (sk_B @ X3) @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i]:
% 0.20/0.49         (((k1_funct_1 @ (sk_B_2 @ X7) @ X8) = (k1_xboole_0))
% 0.20/0.49          | ~ (r2_hidden @ X8 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_relat_1 @ X0)
% 0.20/0.49          | ((k1_funct_1 @ (sk_B_2 @ X0) @ (sk_B @ X0)) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf(s3_funct_1__e7_25__funct_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ?[B:$i]:
% 0.20/0.49       ( ( ![C:$i]:
% 0.20/0.49           ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( np__1 ) ) ) ) & 
% 0.20/0.49         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.20/0.49         ( v1_relat_1 @ B ) ) ))).
% 0.20/0.49  thf('12', plain, (![X9 : $i]: ((k1_relat_1 @ (sk_B_3 @ X9)) = (X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.20/0.49  thf('13', plain, (![X7 : $i]: ((k1_relat_1 @ (sk_B_2 @ X7)) = (X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.49  thf(t16_funct_1, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ![B:$i]:
% 0.20/0.49         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.49               ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.49                   ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.20/0.49                 ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.20/0.49       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ![B:$i]:
% 0.20/0.49            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.49              ( ![C:$i]:
% 0.20/0.49                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.49                  ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.49                      ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.20/0.49                    ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.20/0.49          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t16_funct_1])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X11 : $i, X12 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X11)
% 0.20/0.49          | ~ (v1_funct_1 @ X11)
% 0.20/0.49          | ((X12) = (X11))
% 0.20/0.49          | ((k1_relat_1 @ X11) != (sk_A_1))
% 0.20/0.49          | ((k1_relat_1 @ X12) != (sk_A_1))
% 0.20/0.49          | ~ (v1_funct_1 @ X12)
% 0.20/0.49          | ~ (v1_relat_1 @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((X0) != (sk_A_1))
% 0.20/0.49          | ~ (v1_relat_1 @ X1)
% 0.20/0.49          | ~ (v1_funct_1 @ X1)
% 0.20/0.49          | ((k1_relat_1 @ X1) != (sk_A_1))
% 0.20/0.49          | ((X1) = (sk_B_2 @ X0))
% 0.20/0.49          | ~ (v1_funct_1 @ (sk_B_2 @ X0))
% 0.20/0.49          | ~ (v1_relat_1 @ (sk_B_2 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('16', plain, (![X7 : $i]: (v1_funct_1 @ (sk_B_2 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.49  thf('17', plain, (![X7 : $i]: (v1_relat_1 @ (sk_B_2 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((X0) != (sk_A_1))
% 0.20/0.49          | ~ (v1_relat_1 @ X1)
% 0.20/0.49          | ~ (v1_funct_1 @ X1)
% 0.20/0.49          | ((k1_relat_1 @ X1) != (sk_A_1))
% 0.20/0.49          | ((X1) = (sk_B_2 @ X0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X1 : $i]:
% 0.20/0.49         (((X1) = (sk_B_2 @ sk_A_1))
% 0.20/0.49          | ((k1_relat_1 @ X1) != (sk_A_1))
% 0.20/0.49          | ~ (v1_funct_1 @ X1)
% 0.20/0.49          | ~ (v1_relat_1 @ X1))),
% 0.20/0.49      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((X0) != (sk_A_1))
% 0.20/0.49          | ~ (v1_relat_1 @ (sk_B_3 @ X0))
% 0.20/0.49          | ~ (v1_funct_1 @ (sk_B_3 @ X0))
% 0.20/0.49          | ((sk_B_3 @ X0) = (sk_B_2 @ sk_A_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['12', '19'])).
% 0.20/0.49  thf('21', plain, (![X9 : $i]: (v1_relat_1 @ (sk_B_3 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.20/0.49  thf('22', plain, (![X9 : $i]: (v1_funct_1 @ (sk_B_3 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X0 : $i]: (((X0) != (sk_A_1)) | ((sk_B_3 @ X0) = (sk_B_2 @ sk_A_1)))),
% 0.20/0.49      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.20/0.49  thf('24', plain, (((sk_B_3 @ sk_A_1) = (sk_B_2 @ sk_A_1))),
% 0.20/0.49      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X3 : $i]: ((v1_relat_1 @ X3) | (r2_hidden @ (sk_B @ X3) @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i]:
% 0.20/0.49         (((k1_funct_1 @ (sk_B_3 @ X9) @ X10) = (np__1))
% 0.20/0.49          | ~ (r2_hidden @ X10 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_relat_1 @ X0)
% 0.20/0.49          | ((k1_funct_1 @ (sk_B_3 @ X0) @ (sk_B @ X0)) = (np__1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      ((((k1_funct_1 @ (sk_B_2 @ sk_A_1) @ (sk_B @ sk_A_1)) = (np__1))
% 0.20/0.49        | (v1_relat_1 @ sk_A_1))),
% 0.20/0.49      inference('sup+', [status(thm)], ['24', '27'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      ((((k1_xboole_0) = (np__1))
% 0.20/0.49        | (v1_relat_1 @ sk_A_1)
% 0.20/0.49        | (v1_relat_1 @ sk_A_1))),
% 0.20/0.49      inference('sup+', [status(thm)], ['11', '28'])).
% 0.20/0.49  thf('30', plain, (((v1_relat_1 @ sk_A_1) | ((k1_xboole_0) = (np__1)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['29'])).
% 0.20/0.49  thf('31', plain, (((sk_B_3 @ sk_A_1) = (sk_B_2 @ sk_A_1))),
% 0.20/0.49      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (![X6 : $i]:
% 0.20/0.49         ((r2_hidden @ (k4_tarski @ (sk_B_1 @ X6) @ (sk_C_1 @ X6)) @ X6)
% 0.20/0.49          | ((X6) = (k1_xboole_0))
% 0.20/0.49          | ~ (v1_relat_1 @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i]:
% 0.20/0.49         (((k1_funct_1 @ (sk_B_3 @ X9) @ X10) = (np__1))
% 0.20/0.49          | ~ (r2_hidden @ X10 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X0)
% 0.20/0.49          | ((X0) = (k1_xboole_0))
% 0.20/0.49          | ((k1_funct_1 @ (sk_B_3 @ X0) @ 
% 0.20/0.49              (k4_tarski @ (sk_B_1 @ X0) @ (sk_C_1 @ X0))) = (np__1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      ((((k1_funct_1 @ (sk_B_2 @ sk_A_1) @ 
% 0.20/0.49          (k4_tarski @ (sk_B_1 @ sk_A_1) @ (sk_C_1 @ sk_A_1))) = (np__1))
% 0.20/0.49        | ((sk_A_1) = (k1_xboole_0))
% 0.20/0.49        | ~ (v1_relat_1 @ sk_A_1))),
% 0.20/0.49      inference('sup+', [status(thm)], ['31', '34'])).
% 0.20/0.49  thf('36', plain, (((sk_A_1) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      ((((k1_funct_1 @ (sk_B_2 @ sk_A_1) @ 
% 0.20/0.49          (k4_tarski @ (sk_B_1 @ sk_A_1) @ (sk_C_1 @ sk_A_1))) = (np__1))
% 0.20/0.49        | ~ (v1_relat_1 @ sk_A_1))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      ((((k1_xboole_0) = (np__1))
% 0.20/0.49        | ((k1_funct_1 @ (sk_B_2 @ sk_A_1) @ 
% 0.20/0.49            (k4_tarski @ (sk_B_1 @ sk_A_1) @ (sk_C_1 @ sk_A_1))) = (np__1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['30', '37'])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      ((((k1_xboole_0) = (np__1))
% 0.20/0.49        | ((sk_A_1) = (k1_xboole_0))
% 0.20/0.49        | ~ (v1_relat_1 @ sk_A_1)
% 0.20/0.49        | ((k1_xboole_0) = (np__1)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['8', '38'])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ sk_A_1)
% 0.20/0.49        | ((sk_A_1) = (k1_xboole_0))
% 0.20/0.49        | ((k1_xboole_0) = (np__1)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.49  thf('41', plain, (((sk_A_1) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('42', plain, ((~ (v1_relat_1 @ sk_A_1) | ((k1_xboole_0) = (np__1)))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.20/0.49  thf('43', plain, (((v1_relat_1 @ sk_A_1) | ((k1_xboole_0) = (np__1)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['29'])).
% 0.20/0.49  thf('44', plain, (((k1_xboole_0) = (np__1))),
% 0.20/0.49      inference('clc', [status(thm)], ['42', '43'])).
% 0.20/0.49  thf('45', plain, ((v1_xboole_0 @ np__1)),
% 0.20/0.49      inference('demod', [status(thm)], ['5', '44'])).
% 0.20/0.49  thf('46', plain, ($false), inference('demod', [status(thm)], ['0', '45'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
