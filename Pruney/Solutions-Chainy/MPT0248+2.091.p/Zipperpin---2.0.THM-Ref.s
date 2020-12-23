%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lN9nvWtbp1

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 251 expanded)
%              Number of leaves         :   21 (  72 expanded)
%              Depth                    :   17
%              Number of atoms          :  620 (2820 expanded)
%              Number of equality atoms :  124 ( 608 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k2_xboole_0 @ X23 @ X24 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('2',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('4',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('5',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X20: $i] :
      ( ( k3_xboole_0 @ X20 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('9',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['4','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ X15 @ ( k2_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['10','14'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('16',plain,(
    ! [X42: $i,X43: $i] :
      ( ( X43
        = ( k1_tarski @ X42 ) )
      | ( X43 = k1_xboole_0 )
      | ~ ( r1_tarski @ X43 @ ( k1_tarski @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('17',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('21',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('25',plain,(
    r1_tarski @ sk_C_2 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X42: $i,X43: $i] :
      ( ( X43
        = ( k1_tarski @ X42 ) )
      | ( X43 = k1_xboole_0 )
      | ~ ( r1_tarski @ X43 @ ( k1_tarski @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('27',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_C_2
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,
    ( ( ( sk_C_2 != sk_C_2 )
      | ( sk_C_2 = k1_xboole_0 ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('33',plain,
    ( ( sk_C_2 != sk_C_2 )
   <= ( ( sk_C_2
       != ( k1_tarski @ sk_A ) )
      & ( sk_C_2 != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_C_2
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    sk_B
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['20','22','34'])).

thf('36',plain,(
    sk_B
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['19','35'])).

thf('37',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('38',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('39',plain,(
    ! [X21: $i] :
      ( r1_tarski @ k1_xboole_0 @ X21 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('40',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_xboole_0 @ X19 @ X18 )
        = X18 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k2_xboole_0 @ X23 @ X24 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_C_2 @ X0 )
        = k1_xboole_0 )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['38','43'])).

thf('45',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_C_2 @ X0 )
        = sk_C_2 )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ X0 @ sk_C_2 )
        = ( k5_xboole_0 @ X0 @ sk_C_2 ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('50',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ sk_C_2 )
        = X0 )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('53',plain,
    ( ! [X0: $i] :
        ( X0
        = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ sk_C_2 ) ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('55',plain,(
    ! [X20: $i] :
      ( ( k3_xboole_0 @ X20 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ X0 @ sk_C_2 )
        = k1_xboole_0 )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ X0 @ sk_C_2 )
        = sk_C_2 )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( X0
        = ( k5_xboole_0 @ X0 @ sk_C_2 ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','58'])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ X0 @ sk_C_2 )
        = X0 )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','59'])).

thf('61',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_B )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['18'])).

thf('64',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_C_2
       != ( k1_tarski @ sk_A ) )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_C_2
      = ( k1_tarski @ sk_A ) )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['28'])).

thf('67',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['20','22','34','65','66'])).

thf('68',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['37','67'])).

thf('69',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['17','36','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lN9nvWtbp1
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:14:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 231 iterations in 0.090s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.56  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.56  thf(t43_zfmisc_1, conjecture,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.21/0.56          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.56          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.56          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.56        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.21/0.56             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.56             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.56             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.21/0.56  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t46_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.21/0.56  thf('1', plain,
% 0.21/0.56      (![X23 : $i, X24 : $i]:
% 0.21/0.56         ((k4_xboole_0 @ X23 @ (k2_xboole_0 @ X23 @ X24)) = (k1_xboole_0))),
% 0.21/0.56      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.21/0.56      inference('sup+', [status(thm)], ['0', '1'])).
% 0.21/0.56  thf(t98_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      (![X25 : $i, X26 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ X25 @ X26)
% 0.21/0.56           = (k5_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.21/0.56         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))),
% 0.21/0.56      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.56  thf(t3_boole, axiom,
% 0.21/0.56    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.56  thf('5', plain, (![X22 : $i]: ((k4_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.56  thf(t100_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (![X13 : $i, X14 : $i]:
% 0.21/0.56         ((k4_xboole_0 @ X13 @ X14)
% 0.21/0.56           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((X0) = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.56  thf(t2_boole, axiom,
% 0.21/0.56    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.56  thf('8', plain,
% 0.21/0.56      (![X20 : $i]: ((k3_xboole_0 @ X20 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.56      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.56  thf('9', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.56      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.56  thf('10', plain,
% 0.21/0.56      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['4', '9'])).
% 0.21/0.56  thf(d10_xboole_0, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.56  thf('11', plain,
% 0.21/0.56      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.56  thf('12', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.21/0.56      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.56  thf(t10_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.56         (~ (r1_tarski @ X15 @ X16)
% 0.21/0.56          | (r1_tarski @ X15 @ (k2_xboole_0 @ X17 @ X16)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.56  thf('15', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.21/0.56      inference('sup+', [status(thm)], ['10', '14'])).
% 0.21/0.56  thf(l3_zfmisc_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.56       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      (![X42 : $i, X43 : $i]:
% 0.21/0.56         (((X43) = (k1_tarski @ X42))
% 0.21/0.56          | ((X43) = (k1_xboole_0))
% 0.21/0.56          | ~ (r1_tarski @ X43 @ (k1_tarski @ X42)))),
% 0.21/0.56      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('19', plain,
% 0.21/0.56      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.56      inference('split', [status(esa)], ['18'])).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      (~ (((sk_B) = (k1_tarski @ sk_A))) | ~ (((sk_C_2) = (k1_xboole_0)))),
% 0.21/0.56      inference('split', [status(esa)], ['18'])).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      (~ (((sk_B) = (k1_tarski @ sk_A))) | ~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.21/0.56      inference('split', [status(esa)], ['21'])).
% 0.21/0.56  thf('23', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.56  thf('25', plain, ((r1_tarski @ sk_C_2 @ (k1_tarski @ sk_A))),
% 0.21/0.56      inference('sup+', [status(thm)], ['23', '24'])).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      (![X42 : $i, X43 : $i]:
% 0.21/0.56         (((X43) = (k1_tarski @ X42))
% 0.21/0.56          | ((X43) = (k1_xboole_0))
% 0.21/0.56          | ~ (r1_tarski @ X43 @ (k1_tarski @ X42)))),
% 0.21/0.56      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      ((((sk_C_2) = (k1_xboole_0)) | ((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      ((((sk_B) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('29', plain,
% 0.21/0.56      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 0.21/0.56         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.21/0.56      inference('split', [status(esa)], ['28'])).
% 0.21/0.56  thf('30', plain,
% 0.21/0.56      (((((sk_C_2) != (sk_C_2)) | ((sk_C_2) = (k1_xboole_0))))
% 0.21/0.56         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['27', '29'])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      ((((sk_C_2) = (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.21/0.56      inference('simplify', [status(thm)], ['30'])).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.21/0.56      inference('split', [status(esa)], ['18'])).
% 0.21/0.56  thf('33', plain,
% 0.21/0.56      ((((sk_C_2) != (sk_C_2)))
% 0.21/0.56         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))) & 
% 0.21/0.56             ~ (((sk_C_2) = (k1_xboole_0))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.56  thf('34', plain,
% 0.21/0.56      ((((sk_C_2) = (k1_xboole_0))) | (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['33'])).
% 0.21/0.56  thf('35', plain, (~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.56      inference('sat_resolution*', [status(thm)], ['20', '22', '34'])).
% 0.21/0.56  thf('36', plain, (((sk_B) != (k1_tarski @ sk_A))),
% 0.21/0.56      inference('simpl_trail', [status(thm)], ['19', '35'])).
% 0.21/0.56  thf('37', plain,
% 0.21/0.56      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.21/0.56      inference('split', [status(esa)], ['28'])).
% 0.21/0.56  thf('38', plain,
% 0.21/0.56      ((((sk_C_2) = (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.21/0.56      inference('simplify', [status(thm)], ['30'])).
% 0.21/0.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.56  thf('39', plain, (![X21 : $i]: (r1_tarski @ k1_xboole_0 @ X21)),
% 0.21/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.56  thf(t12_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.56  thf('40', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i]:
% 0.21/0.56         (((k2_xboole_0 @ X19 @ X18) = (X18)) | ~ (r1_tarski @ X19 @ X18))),
% 0.21/0.56      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.56  thf('41', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.56  thf('42', plain,
% 0.21/0.56      (![X23 : $i, X24 : $i]:
% 0.21/0.56         ((k4_xboole_0 @ X23 @ (k2_xboole_0 @ X23 @ X24)) = (k1_xboole_0))),
% 0.21/0.56      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.21/0.56  thf('43', plain,
% 0.21/0.56      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.56      inference('sup+', [status(thm)], ['41', '42'])).
% 0.21/0.56  thf('44', plain,
% 0.21/0.56      ((![X0 : $i]: ((k4_xboole_0 @ sk_C_2 @ X0) = (k1_xboole_0)))
% 0.21/0.56         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.21/0.56      inference('sup+', [status(thm)], ['38', '43'])).
% 0.21/0.56  thf('45', plain,
% 0.21/0.56      ((((sk_C_2) = (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.21/0.56      inference('simplify', [status(thm)], ['30'])).
% 0.21/0.56  thf('46', plain,
% 0.21/0.56      ((![X0 : $i]: ((k4_xboole_0 @ sk_C_2 @ X0) = (sk_C_2)))
% 0.21/0.56         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.21/0.56      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.56  thf('47', plain,
% 0.21/0.56      (![X25 : $i, X26 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ X25 @ X26)
% 0.21/0.56           = (k5_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.56  thf('48', plain,
% 0.21/0.56      ((![X0 : $i]: ((k2_xboole_0 @ X0 @ sk_C_2) = (k5_xboole_0 @ X0 @ sk_C_2)))
% 0.21/0.56         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.21/0.56      inference('sup+', [status(thm)], ['46', '47'])).
% 0.21/0.56  thf('49', plain,
% 0.21/0.56      ((((sk_C_2) = (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.21/0.56      inference('simplify', [status(thm)], ['30'])).
% 0.21/0.56  thf('50', plain, (![X22 : $i]: ((k4_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.56  thf('51', plain,
% 0.21/0.56      ((![X0 : $i]: ((k4_xboole_0 @ X0 @ sk_C_2) = (X0)))
% 0.21/0.56         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.21/0.56      inference('sup+', [status(thm)], ['49', '50'])).
% 0.21/0.56  thf('52', plain,
% 0.21/0.56      (![X13 : $i, X14 : $i]:
% 0.21/0.56         ((k4_xboole_0 @ X13 @ X14)
% 0.21/0.56           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.56  thf('53', plain,
% 0.21/0.56      ((![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ sk_C_2))))
% 0.21/0.56         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.21/0.56      inference('sup+', [status(thm)], ['51', '52'])).
% 0.21/0.56  thf('54', plain,
% 0.21/0.56      ((((sk_C_2) = (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.21/0.56      inference('simplify', [status(thm)], ['30'])).
% 0.21/0.56  thf('55', plain,
% 0.21/0.56      (![X20 : $i]: ((k3_xboole_0 @ X20 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.56      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.56  thf('56', plain,
% 0.21/0.56      ((![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_C_2) = (k1_xboole_0)))
% 0.21/0.56         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.21/0.56      inference('sup+', [status(thm)], ['54', '55'])).
% 0.21/0.56  thf('57', plain,
% 0.21/0.56      ((((sk_C_2) = (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.21/0.56      inference('simplify', [status(thm)], ['30'])).
% 0.21/0.56  thf('58', plain,
% 0.21/0.56      ((![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_C_2) = (sk_C_2)))
% 0.21/0.56         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.21/0.56      inference('demod', [status(thm)], ['56', '57'])).
% 0.21/0.56  thf('59', plain,
% 0.21/0.56      ((![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ sk_C_2)))
% 0.21/0.56         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.21/0.56      inference('demod', [status(thm)], ['53', '58'])).
% 0.21/0.56  thf('60', plain,
% 0.21/0.56      ((![X0 : $i]: ((k2_xboole_0 @ X0 @ sk_C_2) = (X0)))
% 0.21/0.56         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.21/0.56      inference('demod', [status(thm)], ['48', '59'])).
% 0.21/0.56  thf('61', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('62', plain,
% 0.21/0.56      ((((k1_tarski @ sk_A) = (sk_B))) <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.21/0.56      inference('sup+', [status(thm)], ['60', '61'])).
% 0.21/0.56  thf('63', plain,
% 0.21/0.56      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.56      inference('split', [status(esa)], ['18'])).
% 0.21/0.56  thf('64', plain,
% 0.21/0.56      ((((sk_B) != (sk_B)))
% 0.21/0.56         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))) & 
% 0.21/0.56             ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.56  thf('65', plain,
% 0.21/0.56      ((((sk_C_2) = (k1_tarski @ sk_A))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['64'])).
% 0.21/0.56  thf('66', plain,
% 0.21/0.56      (~ (((sk_B) = (k1_xboole_0))) | ~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.21/0.56      inference('split', [status(esa)], ['28'])).
% 0.21/0.56  thf('67', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.21/0.56      inference('sat_resolution*', [status(thm)],
% 0.21/0.56                ['20', '22', '34', '65', '66'])).
% 0.21/0.56  thf('68', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.56      inference('simpl_trail', [status(thm)], ['37', '67'])).
% 0.21/0.56  thf('69', plain, ($false),
% 0.21/0.56      inference('simplify_reflect-', [status(thm)], ['17', '36', '68'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.39/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
