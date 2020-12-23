%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MmukQIbVQu

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 180 expanded)
%              Number of leaves         :   28 (  68 expanded)
%              Depth                    :   16
%              Number of atoms          :  429 (1397 expanded)
%              Number of equality atoms :   48 ( 205 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v5_funct_1_type,type,(
    v5_funct_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('0',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( ( k1_relat_1 @ X7 )
       != k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( sk_B @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('7',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['5','6'])).

thf(d20_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( v5_funct_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
               => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X12 ) @ ( k1_relat_1 @ X11 ) )
      | ( v5_funct_1 @ X11 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d20_funct_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['4'])).

thf('11',plain,(
    ! [X16: $i] :
      ( v1_funct_1 @ ( sk_B @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('12',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['4'])).

thf('14',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( sk_B @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('15',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','12','15'])).

thf('17',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('18',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X4 ) )
      | ( ( k11_relat_1 @ X4 @ X5 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['13','14'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X0 @ X1 )
        = ( k9_relat_1 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(t62_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
          = k1_xboole_0 )
        & ( ( k5_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ) )).

thf('23',plain,(
    ! [X6: $i] :
      ( ( ( k5_relat_1 @ X6 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t62_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('24',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k7_relat_1 @ X10 @ X9 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X9 ) @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('26',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('27',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['13','14'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X3 ) )
        = ( k9_relat_1 @ X2 @ X3 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('32',plain,(
    ! [X8: $i] :
      ( ( ( k1_relat_1 @ X8 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X8 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['13','14'])).

thf('35',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['13','14'])).

thf('38',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k11_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','38'])).

thf('40',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['13','14'])).

thf('41',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k11_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( k1_xboole_0 != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','43'])).

thf(t174_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( v5_funct_1 @ k1_xboole_0 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( v5_funct_1 @ k1_xboole_0 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t174_funct_1])).

thf('45',plain,(
    ~ ( v5_funct_1 @ k1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['46','47','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MmukQIbVQu
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:24:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 42 iterations in 0.023s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.48  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.20/0.48  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.48  thf(v5_funct_1_type, type, v5_funct_1: $i > $i > $o).
% 0.20/0.48  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ?[B:$i]:
% 0.20/0.48       ( ( ![C:$i]:
% 0.20/0.48           ( ( r2_hidden @ C @ A ) =>
% 0.20/0.48             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.48         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.20/0.48         ( v1_relat_1 @ B ) ) ))).
% 0.20/0.48  thf('0', plain, (![X16 : $i]: ((k1_relat_1 @ (sk_B @ X16)) = (X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.48  thf(t64_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.48           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.48         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X7 : $i]:
% 0.20/0.48         (((k1_relat_1 @ X7) != (k1_xboole_0))
% 0.20/0.48          | ((X7) = (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((X0) != (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.20/0.48          | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.48  thf('3', plain, (![X16 : $i]: (v1_relat_1 @ (sk_B @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.20/0.48      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf('5', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.48  thf('6', plain, (![X16 : $i]: ((k1_relat_1 @ (sk_B @ X16)) = (X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.48  thf('7', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf(d20_funct_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.48           ( ( v5_funct_1 @ B @ A ) <=>
% 0.20/0.48             ( ![C:$i]:
% 0.20/0.48               ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.48                 ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X11)
% 0.20/0.48          | ~ (v1_funct_1 @ X11)
% 0.20/0.48          | (r2_hidden @ (sk_C @ X11 @ X12) @ (k1_relat_1 @ X11))
% 0.20/0.48          | (v5_funct_1 @ X11 @ X12)
% 0.20/0.48          | ~ (v1_funct_1 @ X12)
% 0.20/0.48          | ~ (v1_relat_1 @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [d20_funct_1])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.20/0.48          | ~ (v1_relat_1 @ X0)
% 0.20/0.48          | ~ (v1_funct_1 @ X0)
% 0.20/0.48          | (v5_funct_1 @ k1_xboole_0 @ X0)
% 0.20/0.48          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.20/0.48          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf('10', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.48  thf('11', plain, (![X16 : $i]: (v1_funct_1 @ (sk_B @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.48  thf('12', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.20/0.48      inference('sup+', [status(thm)], ['10', '11'])).
% 0.20/0.48  thf('13', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.48  thf('14', plain, (![X16 : $i]: (v1_relat_1 @ (sk_B @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.48  thf('15', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.48      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.20/0.48          | ~ (v1_relat_1 @ X0)
% 0.20/0.48          | ~ (v1_funct_1 @ X0)
% 0.20/0.48          | (v5_funct_1 @ k1_xboole_0 @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['9', '12', '15'])).
% 0.20/0.48  thf('17', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf(t205_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.20/0.48         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X5 @ (k1_relat_1 @ X4))
% 0.20/0.48          | ((k11_relat_1 @ X4 @ X5) != (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.20/0.48          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.48          | ((k11_relat_1 @ k1_xboole_0 @ X0) != (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('20', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.48      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.20/0.48          | ((k11_relat_1 @ k1_xboole_0 @ X0) != (k1_xboole_0)))),
% 0.20/0.48      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf(d16_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((k11_relat_1 @ X0 @ X1) = (k9_relat_1 @ X0 @ (k1_tarski @ X1)))
% 0.20/0.48          | ~ (v1_relat_1 @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.20/0.48  thf(t62_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.20/0.48         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X6 : $i]:
% 0.20/0.48         (((k5_relat_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [t62_relat_1])).
% 0.20/0.48  thf(t94_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i]:
% 0.20/0.48         (((k7_relat_1 @ X10 @ X9) = (k5_relat_1 @ (k6_relat_1 @ X9) @ X10))
% 0.20/0.48          | ~ (v1_relat_1 @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf(fc3_funct_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.48       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.48  thf('26', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.48  thf('27', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.48      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.20/0.48  thf(t148_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i]:
% 0.20/0.48         (((k2_relat_1 @ (k7_relat_1 @ X2 @ X3)) = (k9_relat_1 @ X2 @ X3))
% 0.20/0.48          | ~ (v1_relat_1 @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['28', '29'])).
% 0.20/0.48  thf('31', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf(t65_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.48         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (![X8 : $i]:
% 0.20/0.48         (((k1_relat_1 @ X8) != (k1_xboole_0))
% 0.20/0.48          | ((k2_relat_1 @ X8) = (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.48        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.48        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.48  thf('34', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.48      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.48        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.48      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.48  thf('36', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['35'])).
% 0.20/0.48  thf('37', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.48      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['30', '36', '37'])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k1_xboole_0) = (k11_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['22', '38'])).
% 0.20/0.48  thf('40', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.48      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      (![X0 : $i]: ((k1_xboole_0) = (k11_relat_1 @ k1_xboole_0 @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X0 @ k1_xboole_0) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.20/0.48      inference('demod', [status(thm)], ['21', '41'])).
% 0.20/0.48  thf('43', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.48      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v5_funct_1 @ k1_xboole_0 @ X0)
% 0.20/0.48          | ~ (v1_funct_1 @ X0)
% 0.20/0.48          | ~ (v1_relat_1 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['16', '43'])).
% 0.20/0.48  thf(t174_funct_1, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.48       ( v5_funct_1 @ k1_xboole_0 @ A ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.48          ( v5_funct_1 @ k1_xboole_0 @ A ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t174_funct_1])).
% 0.20/0.48  thf('45', plain, (~ (v5_funct_1 @ k1_xboole_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('46', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_funct_1 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.48  thf('47', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('48', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('49', plain, ($false),
% 0.20/0.48      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
