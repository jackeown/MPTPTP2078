%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WcfSEcGNXG

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:17 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 108 expanded)
%              Number of leaves         :   25 (  43 expanded)
%              Depth                    :   17
%              Number of atoms          :  547 ( 797 expanded)
%              Number of equality atoms :   61 (  89 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t148_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( ( k3_xboole_0 @ B @ C )
          = ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ A ) )
     => ( ( k3_xboole_0 @ A @ C )
        = ( k1_tarski @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( ( k3_xboole_0 @ B @ C )
            = ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ A ) )
       => ( ( k3_xboole_0 @ A @ C )
          = ( k1_tarski @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t148_zfmisc_1])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['3','4'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k3_xboole_0 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k3_xboole_0 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) @ ( k1_tarski @ sk_D ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ ( k1_tarski @ sk_D ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('16',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('17',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X33
        = ( k1_tarski @ X32 ) )
      | ( X33 = k1_xboole_0 )
      | ~ ( r1_tarski @ X33 @ ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('18',plain,
    ( ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
      = ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C_1 )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ( k3_xboole_0 @ sk_C_1 @ sk_A )
 != ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['18','21'])).

thf('23',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k3_xboole_0 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_A )
    = ( k3_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('28',plain,(
    ! [X18: $i] :
      ( r1_tarski @ k1_xboole_0 @ X18 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['26','27','32'])).

thf('34',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('35',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) ) ),
    inference('sup+',[status(thm)],['33','42'])).

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

thf('44',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('45',plain,(
    ! [X18: $i] :
      ( r1_tarski @ k1_xboole_0 @ X18 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('46',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('48',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ( ( k4_xboole_0 @ X36 @ ( k1_tarski @ X35 ) )
       != X36 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','50'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('52',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) ) ),
    inference(demod,[status(thm)],['43','53'])).

thf('55',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ( ( k4_xboole_0 @ X36 @ ( k1_tarski @ X35 ) )
       != X36 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('56',plain,
    ( ( sk_A != sk_A )
    | ~ ( r2_hidden @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference(simplify,[status(thm)],['58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WcfSEcGNXG
% 0.15/0.38  % Computer   : n014.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 18:11:07 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.24/0.38  % Python version: Python 3.6.8
% 0.24/0.38  % Running in FO mode
% 0.59/0.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.80  % Solved by: fo/fo7.sh
% 0.59/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.80  % done 675 iterations in 0.321s
% 0.59/0.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.80  % SZS output start Refutation
% 0.59/0.80  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.59/0.80  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.59/0.80  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.80  thf(sk_D_type, type, sk_D: $i).
% 0.59/0.80  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.80  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.59/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.80  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.59/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.80  thf(commutativity_k3_xboole_0, axiom,
% 0.59/0.80    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.59/0.80  thf('0', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.80  thf(t148_zfmisc_1, conjecture,
% 0.59/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.80     ( ( ( r1_tarski @ A @ B ) & 
% 0.59/0.80         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.59/0.80         ( r2_hidden @ D @ A ) ) =>
% 0.59/0.80       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 0.59/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.80    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.80        ( ( ( r1_tarski @ A @ B ) & 
% 0.59/0.80            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.59/0.80            ( r2_hidden @ D @ A ) ) =>
% 0.59/0.80          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 0.59/0.80    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 0.59/0.80  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf(t28_xboole_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.59/0.80  thf('2', plain,
% 0.59/0.80      (![X16 : $i, X17 : $i]:
% 0.59/0.80         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.59/0.80      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.80  thf('3', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.59/0.80      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.80  thf('4', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.80  thf('5', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.59/0.80      inference('demod', [status(thm)], ['3', '4'])).
% 0.59/0.80  thf(t16_xboole_1, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i]:
% 0.59/0.80     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.59/0.80       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.59/0.80  thf('6', plain,
% 0.59/0.80      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.59/0.80         ((k3_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13)
% 0.59/0.80           = (k3_xboole_0 @ X11 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.59/0.80      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.59/0.80  thf('7', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((k3_xboole_0 @ sk_A @ X0)
% 0.59/0.80           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['5', '6'])).
% 0.59/0.80  thf('8', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((k3_xboole_0 @ sk_A @ X0)
% 0.59/0.80           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_A)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['0', '7'])).
% 0.59/0.80  thf('9', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_tarski @ sk_D))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('10', plain,
% 0.59/0.80      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.59/0.80         ((k3_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13)
% 0.59/0.80           = (k3_xboole_0 @ X11 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.59/0.80      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.59/0.80  thf(t17_xboole_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.59/0.80  thf('11', plain,
% 0.59/0.80      (![X14 : $i, X15 : $i]: (r1_tarski @ (k3_xboole_0 @ X14 @ X15) @ X14)),
% 0.59/0.80      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.59/0.80  thf('12', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.80         (r1_tarski @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.59/0.80          (k3_xboole_0 @ X2 @ X1))),
% 0.59/0.80      inference('sup+', [status(thm)], ['10', '11'])).
% 0.59/0.80  thf('13', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (r1_tarski @ (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ X0)) @ 
% 0.59/0.80          (k1_tarski @ sk_D))),
% 0.59/0.80      inference('sup+', [status(thm)], ['9', '12'])).
% 0.59/0.80  thf('14', plain,
% 0.59/0.80      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_C_1) @ (k1_tarski @ sk_D))),
% 0.59/0.80      inference('sup+', [status(thm)], ['8', '13'])).
% 0.59/0.80  thf('15', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.80  thf('16', plain,
% 0.59/0.80      ((r1_tarski @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ (k1_tarski @ sk_D))),
% 0.59/0.80      inference('demod', [status(thm)], ['14', '15'])).
% 0.59/0.80  thf(l3_zfmisc_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.59/0.80       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.59/0.80  thf('17', plain,
% 0.59/0.80      (![X32 : $i, X33 : $i]:
% 0.59/0.80         (((X33) = (k1_tarski @ X32))
% 0.59/0.80          | ((X33) = (k1_xboole_0))
% 0.59/0.80          | ~ (r1_tarski @ X33 @ (k1_tarski @ X32)))),
% 0.59/0.80      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.59/0.80  thf('18', plain,
% 0.59/0.80      ((((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))
% 0.59/0.80        | ((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_tarski @ sk_D)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['16', '17'])).
% 0.59/0.80  thf('19', plain, (((k3_xboole_0 @ sk_A @ sk_C_1) != (k1_tarski @ sk_D))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('20', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.80  thf('21', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) != (k1_tarski @ sk_D))),
% 0.59/0.80      inference('demod', [status(thm)], ['19', '20'])).
% 0.59/0.80  thf('22', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 0.59/0.80      inference('simplify_reflect-', [status(thm)], ['18', '21'])).
% 0.59/0.80  thf('23', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_tarski @ sk_D))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('24', plain,
% 0.59/0.80      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.59/0.80         ((k3_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13)
% 0.59/0.80           = (k3_xboole_0 @ X11 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.59/0.80      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.59/0.80  thf('25', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((k3_xboole_0 @ (k1_tarski @ sk_D) @ X0)
% 0.59/0.80           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ X0)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['23', '24'])).
% 0.59/0.80  thf('26', plain,
% 0.59/0.80      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_A)
% 0.59/0.80         = (k3_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['22', '25'])).
% 0.59/0.80  thf('27', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.80  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.59/0.80  thf('28', plain, (![X18 : $i]: (r1_tarski @ k1_xboole_0 @ X18)),
% 0.59/0.80      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.59/0.80  thf('29', plain,
% 0.59/0.80      (![X16 : $i, X17 : $i]:
% 0.59/0.80         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.59/0.80      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.80  thf('30', plain,
% 0.59/0.80      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['28', '29'])).
% 0.59/0.80  thf('31', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.80  thf('32', plain,
% 0.59/0.80      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['30', '31'])).
% 0.59/0.80  thf('33', plain,
% 0.59/0.80      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)) = (k1_xboole_0))),
% 0.59/0.80      inference('demod', [status(thm)], ['26', '27', '32'])).
% 0.59/0.80  thf('34', plain,
% 0.59/0.80      (![X14 : $i, X15 : $i]: (r1_tarski @ (k3_xboole_0 @ X14 @ X15) @ X14)),
% 0.59/0.80      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.59/0.80  thf('35', plain,
% 0.59/0.80      (![X16 : $i, X17 : $i]:
% 0.59/0.80         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.59/0.80      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.80  thf('36', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.59/0.80           = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.80      inference('sup-', [status(thm)], ['34', '35'])).
% 0.59/0.80  thf('37', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.80  thf('38', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.59/0.80           = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.80      inference('demod', [status(thm)], ['36', '37'])).
% 0.59/0.80  thf(t100_xboole_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.59/0.80  thf('39', plain,
% 0.59/0.80      (![X9 : $i, X10 : $i]:
% 0.59/0.80         ((k4_xboole_0 @ X9 @ X10)
% 0.59/0.80           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.59/0.80      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.59/0.80  thf('40', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.59/0.80           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['38', '39'])).
% 0.59/0.80  thf('41', plain,
% 0.59/0.80      (![X9 : $i, X10 : $i]:
% 0.59/0.80         ((k4_xboole_0 @ X9 @ X10)
% 0.59/0.80           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.59/0.80      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.59/0.80  thf('42', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.59/0.80           = (k4_xboole_0 @ X1 @ X0))),
% 0.59/0.80      inference('demod', [status(thm)], ['40', '41'])).
% 0.59/0.80  thf('43', plain,
% 0.59/0.80      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.59/0.80         = (k4_xboole_0 @ sk_A @ (k1_tarski @ sk_D)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['33', '42'])).
% 0.59/0.80  thf(t3_xboole_0, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.59/0.80            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.59/0.80       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.59/0.80            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.59/0.80  thf('44', plain,
% 0.59/0.80      (![X2 : $i, X3 : $i]:
% 0.59/0.80         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X3))),
% 0.59/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.59/0.80  thf('45', plain, (![X18 : $i]: (r1_tarski @ k1_xboole_0 @ X18)),
% 0.59/0.80      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.59/0.80  thf(l32_xboole_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.59/0.80  thf('46', plain,
% 0.59/0.80      (![X6 : $i, X8 : $i]:
% 0.59/0.80         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.59/0.80      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.59/0.80  thf('47', plain,
% 0.59/0.80      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['45', '46'])).
% 0.59/0.80  thf(t65_zfmisc_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.59/0.80       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.59/0.80  thf('48', plain,
% 0.59/0.80      (![X35 : $i, X36 : $i]:
% 0.59/0.80         (~ (r2_hidden @ X35 @ X36)
% 0.59/0.80          | ((k4_xboole_0 @ X36 @ (k1_tarski @ X35)) != (X36)))),
% 0.59/0.80      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.59/0.80  thf('49', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['47', '48'])).
% 0.59/0.80  thf('50', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.59/0.80      inference('simplify', [status(thm)], ['49'])).
% 0.59/0.80  thf('51', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.59/0.80      inference('sup-', [status(thm)], ['44', '50'])).
% 0.59/0.80  thf(t83_xboole_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.59/0.80  thf('52', plain,
% 0.59/0.80      (![X19 : $i, X20 : $i]:
% 0.59/0.80         (((k4_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_xboole_0 @ X19 @ X20))),
% 0.59/0.80      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.59/0.80  thf('53', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['51', '52'])).
% 0.59/0.80  thf('54', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ (k1_tarski @ sk_D)))),
% 0.59/0.80      inference('demod', [status(thm)], ['43', '53'])).
% 0.59/0.80  thf('55', plain,
% 0.59/0.80      (![X35 : $i, X36 : $i]:
% 0.59/0.80         (~ (r2_hidden @ X35 @ X36)
% 0.59/0.80          | ((k4_xboole_0 @ X36 @ (k1_tarski @ X35)) != (X36)))),
% 0.59/0.80      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.59/0.80  thf('56', plain, ((((sk_A) != (sk_A)) | ~ (r2_hidden @ sk_D @ sk_A))),
% 0.59/0.80      inference('sup-', [status(thm)], ['54', '55'])).
% 0.59/0.80  thf('57', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('58', plain, (((sk_A) != (sk_A))),
% 0.59/0.80      inference('demod', [status(thm)], ['56', '57'])).
% 0.59/0.80  thf('59', plain, ($false), inference('simplify', [status(thm)], ['58'])).
% 0.59/0.80  
% 0.59/0.80  % SZS output end Refutation
% 0.59/0.80  
% 0.59/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
