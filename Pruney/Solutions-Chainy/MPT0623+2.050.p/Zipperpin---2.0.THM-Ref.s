%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hTZtWFLUw0

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 167 expanded)
%              Number of leaves         :   26 (  61 expanded)
%              Depth                    :   18
%              Number of atoms          :  589 (1404 expanded)
%              Number of equality atoms :   82 ( 200 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_4_type,type,(
    sk_C_4: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t15_funct_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ! [B: $i] :
        ? [C: $i] :
          ( ( ( k2_relat_1 @ C )
            = ( k1_tarski @ B ) )
          & ( ( k1_relat_1 @ C )
            = A )
          & ( v1_funct_1 @ C )
          & ( v1_relat_1 @ C ) ) ) )).

thf('0',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_4 @ X19 @ X20 ) )
        = X20 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_funct_1 @ ( sk_C_4 @ X19 @ X20 ) )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('3',plain,(
    ! [X10: $i] :
      ( r1_xboole_0 @ X10 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( X12 != X11 )
      | ( r2_hidden @ X12 @ X13 )
      | ( X13
       != ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('5',plain,(
    ! [X11: $i] :
      ( r2_hidden @ X11 @ ( k1_tarski @ X11 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( X14 = X11 )
      | ( X13
       != ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('12',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14 = X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C_1 @ k1_xboole_0 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_4 @ X19 @ X20 ) )
        = ( k1_tarski @ X19 ) )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(t18_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( ( A = k1_xboole_0 )
            & ( B != k1_xboole_0 ) )
        & ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ~ ( ( B
                  = ( k1_relat_1 @ C ) )
                & ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ~ ( ( A = k1_xboole_0 )
              & ( B != k1_xboole_0 ) )
          & ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ~ ( ( B
                    = ( k1_relat_1 @ C ) )
                  & ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_funct_1])).

thf('19',plain,(
    ! [X21: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X21 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_4 @ X0 @ X1 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_4 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('25',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('26',plain,(
    ! [X21: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X21 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1
     != ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

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

thf('28',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('29',plain,(
    ! [X16: $i] :
      ( ( ( k1_relat_1 @ X16 )
       != k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('35',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['32'])).

thf('37',plain,(
    ! [X17: $i] :
      ( v1_funct_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('38',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('40',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','35','38','39'])).

thf('41',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('42',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','44'])).

thf('46',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('48',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['46','47'])).

thf('49',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['23','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_4 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['21','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ X0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_relat_1 @ ( sk_C_4 @ X19 @ X20 ) )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','54'])).

thf('56',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['40','43'])).

thf('58',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['56','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hTZtWFLUw0
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:22:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 100 iterations in 0.049s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(sk_C_4_type, type, sk_C_4: $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.51  thf(t15_funct_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ?[C:$i]:
% 0.21/0.51           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.21/0.51             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.21/0.51             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (![X19 : $i, X20 : $i]:
% 0.21/0.51         (((k1_relat_1 @ (sk_C_4 @ X19 @ X20)) = (X20))
% 0.21/0.51          | ((X20) = (k1_xboole_0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X19 : $i, X20 : $i]:
% 0.21/0.51         ((v1_funct_1 @ (sk_C_4 @ X19 @ X20)) | ((X20) = (k1_xboole_0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.51  thf(t2_tarski, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.21/0.51       ( ( A ) = ( B ) ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i]:
% 0.21/0.51         (((X5) = (X4))
% 0.21/0.51          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 0.21/0.51          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_tarski])).
% 0.21/0.51  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.51  thf('3', plain, (![X10 : $i]: (r1_xboole_0 @ X10 @ k1_xboole_0)),
% 0.21/0.51      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.51  thf(d1_tarski, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.51         (((X12) != (X11))
% 0.21/0.51          | (r2_hidden @ X12 @ X13)
% 0.21/0.51          | ((X13) != (k1_tarski @ X11)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.51  thf('5', plain, (![X11 : $i]: (r2_hidden @ X11 @ (k1_tarski @ X11))),
% 0.21/0.51      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.51  thf(t3_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.51            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.51       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.51            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X8 @ X6)
% 0.21/0.51          | ~ (r2_hidden @ X8 @ X9)
% 0.21/0.51          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.51  thf('8', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '7'])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0)
% 0.21/0.51          | ((X0) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '8'])).
% 0.21/0.51  thf(d3_tarski, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X1 : $i, X3 : $i]:
% 0.21/0.51         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X14 @ X13)
% 0.21/0.51          | ((X14) = (X11))
% 0.21/0.51          | ((X13) != (k1_tarski @ X11)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X11 : $i, X14 : $i]:
% 0.21/0.51         (((X14) = (X11)) | ~ (r2_hidden @ X14 @ (k1_tarski @ X11)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.21/0.51          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['10', '12'])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X1 : $i, X3 : $i]:
% 0.21/0.51         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.51          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.21/0.51          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.51      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((X0) = (k1_xboole_0))
% 0.21/0.51          | (r1_tarski @ (k1_tarski @ (sk_C_1 @ k1_xboole_0 @ X0)) @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['9', '16'])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X19 : $i, X20 : $i]:
% 0.21/0.51         (((k2_relat_1 @ (sk_C_4 @ X19 @ X20)) = (k1_tarski @ X19))
% 0.21/0.51          | ((X20) = (k1_xboole_0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.51  thf(t18_funct_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.51          ( ![C:$i]:
% 0.21/0.51            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.51              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.21/0.51                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i]:
% 0.21/0.51        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.51             ( ![C:$i]:
% 0.21/0.51               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.51                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.21/0.51                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X21 : $i]:
% 0.21/0.51         (~ (r1_tarski @ (k2_relat_1 @ X21) @ sk_A)
% 0.21/0.51          | ((sk_B_1) != (k1_relat_1 @ X21))
% 0.21/0.51          | ~ (v1_funct_1 @ X21)
% 0.21/0.51          | ~ (v1_relat_1 @ X21))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.21/0.51          | ((X1) = (k1_xboole_0))
% 0.21/0.51          | ~ (v1_relat_1 @ (sk_C_4 @ X0 @ X1))
% 0.21/0.51          | ~ (v1_funct_1 @ (sk_C_4 @ X0 @ X1))
% 0.21/0.51          | ((sk_B_1) != (k1_relat_1 @ (sk_C_4 @ X0 @ X1))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((sk_A) = (k1_xboole_0))
% 0.21/0.51          | ((sk_B_1)
% 0.21/0.51              != (k1_relat_1 @ (sk_C_4 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ X0)))
% 0.21/0.51          | ~ (v1_funct_1 @ (sk_C_4 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ X0))
% 0.21/0.51          | ~ (v1_relat_1 @ (sk_C_4 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ X0))
% 0.21/0.51          | ((X0) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['17', '20'])).
% 0.21/0.51  thf('22', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.21/0.51      inference('split', [status(esa)], ['22'])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('split', [status(esa)], ['22'])).
% 0.21/0.51  thf(t60_relat_1, axiom,
% 0.21/0.51    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.51     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.51  thf('25', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X21 : $i]:
% 0.21/0.51         (~ (r1_tarski @ (k2_relat_1 @ X21) @ sk_A)
% 0.21/0.51          | ((sk_B_1) != (k1_relat_1 @ X21))
% 0.21/0.51          | ~ (v1_funct_1 @ X21)
% 0.21/0.51          | ~ (v1_relat_1 @ X21))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.21/0.51        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.51        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.51        | ((sk_B_1) != (k1_relat_1 @ k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.51  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ?[B:$i]:
% 0.21/0.51       ( ( ![C:$i]:
% 0.21/0.51           ( ( r2_hidden @ C @ A ) =>
% 0.21/0.51             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.51         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.21/0.51         ( v1_relat_1 @ B ) ) ))).
% 0.21/0.51  thf('28', plain, (![X17 : $i]: ((k1_relat_1 @ (sk_B @ X17)) = (X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.51  thf(t64_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) =>
% 0.21/0.51       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.51           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.51         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X16 : $i]:
% 0.21/0.51         (((k1_relat_1 @ X16) != (k1_xboole_0))
% 0.21/0.51          | ((X16) = (k1_xboole_0))
% 0.21/0.51          | ~ (v1_relat_1 @ X16))),
% 0.21/0.51      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((X0) != (k1_xboole_0))
% 0.21/0.51          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.21/0.51          | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.51  thf('31', plain, (![X17 : $i]: (v1_relat_1 @ (sk_B @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.51  thf('33', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.51  thf('34', plain, (![X17 : $i]: (v1_relat_1 @ (sk_B @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.51  thf('35', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.51      inference('sup+', [status(thm)], ['33', '34'])).
% 0.21/0.51  thf('36', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.51  thf('37', plain, (![X17 : $i]: (v1_funct_1 @ (sk_B @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.51  thf('38', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.21/0.51      inference('sup+', [status(thm)], ['36', '37'])).
% 0.21/0.51  thf('39', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      ((~ (r1_tarski @ k1_xboole_0 @ sk_A) | ((sk_B_1) != (k1_xboole_0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['27', '35', '38', '39'])).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      (![X1 : $i, X3 : $i]:
% 0.21/0.51         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.51  thf('42', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '7'])).
% 0.21/0.51  thf('43', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.51  thf('44', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['40', '43'])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      ((((sk_B_1) != (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['24', '44'])).
% 0.21/0.51  thf('46', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.51      inference('split', [status(esa)], ['22'])).
% 0.21/0.51  thf('48', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['46', '47'])).
% 0.21/0.51  thf('49', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['23', '48'])).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((sk_B_1)
% 0.21/0.51            != (k1_relat_1 @ (sk_C_4 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ X0)))
% 0.21/0.51          | ~ (v1_funct_1 @ (sk_C_4 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ X0))
% 0.21/0.51          | ~ (v1_relat_1 @ (sk_C_4 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ X0))
% 0.21/0.51          | ((X0) = (k1_xboole_0)))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['21', '49'])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((X0) = (k1_xboole_0))
% 0.21/0.51          | ((X0) = (k1_xboole_0))
% 0.21/0.51          | ~ (v1_relat_1 @ (sk_C_4 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ X0))
% 0.21/0.51          | ((sk_B_1)
% 0.21/0.51              != (k1_relat_1 @ (sk_C_4 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ X0))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '50'])).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((sk_B_1)
% 0.21/0.51            != (k1_relat_1 @ (sk_C_4 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ X0)))
% 0.21/0.51          | ~ (v1_relat_1 @ (sk_C_4 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ X0))
% 0.21/0.51          | ((X0) = (k1_xboole_0)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['51'])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      (![X19 : $i, X20 : $i]:
% 0.21/0.51         ((v1_relat_1 @ (sk_C_4 @ X19 @ X20)) | ((X20) = (k1_xboole_0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((X0) = (k1_xboole_0))
% 0.21/0.51          | ((sk_B_1)
% 0.21/0.51              != (k1_relat_1 @ (sk_C_4 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ X0))))),
% 0.21/0.51      inference('clc', [status(thm)], ['52', '53'])).
% 0.21/0.51  thf('55', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((sk_B_1) != (X0)) | ((X0) = (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '54'])).
% 0.21/0.51  thf('56', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['55'])).
% 0.21/0.51  thf('57', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['40', '43'])).
% 0.21/0.51  thf('58', plain, ($false),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['56', '57'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
