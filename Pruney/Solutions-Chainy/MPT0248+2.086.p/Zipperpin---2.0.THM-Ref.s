%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pcMe9GdFht

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:30 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 234 expanded)
%              Number of leaves         :   21 (  69 expanded)
%              Depth                    :   18
%              Number of atoms          :  652 (2744 expanded)
%              Number of equality atoms :  128 ( 619 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t93_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('4',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('5',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('9',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('10',plain,(
    ! [X45: $i,X46: $i] :
      ( ( X46
        = ( k1_tarski @ X45 ) )
      | ( X46 = k1_xboole_0 )
      | ~ ( r1_tarski @ X46 @ ( k1_tarski @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('11',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C @ sk_B ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','16'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('19',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('20',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C )
      = sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18','25'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('27',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('28',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('30',plain,(
    ! [X45: $i,X46: $i] :
      ( ( X46
        = ( k1_tarski @ X45 ) )
      | ( X46 = k1_xboole_0 )
      | ~ ( r1_tarski @ X46 @ ( k1_tarski @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( sk_B = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C
      = ( k1_tarski @ sk_A ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_C
      = ( k1_tarski @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('37',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['37'])).

thf('39',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('40',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['40'])).

thf('42',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('45',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['36','38','46'])).

thf('48',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['35','47'])).

thf('49',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['40'])).

thf('50',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('52',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ X0 @ sk_B )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( sk_B
        = ( k5_xboole_0 @ X0 @ X0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ X0 @ X0 )
        = ( k2_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ X0 ) ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('59',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('60',plain,
    ( ! [X0: $i] :
        ( X0
        = ( k2_xboole_0 @ sk_B @ X0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( sk_C
      = ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['50','60'])).

thf('62',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['35','47'])).

thf('63',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_C != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['40'])).

thf('65',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['63','64'])).

thf('66',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['49','65'])).

thf('67',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['33','48','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['6','67'])).

thf('69',plain,
    ( ( k1_tarski @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['0','68'])).

thf('70',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['35','47'])).

thf('71',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['69','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pcMe9GdFht
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:59:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 124 iterations in 0.035s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(t43_zfmisc_1, conjecture,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.19/0.48          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.19/0.48          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.19/0.48          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.48        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.19/0.48             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.19/0.48             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.19/0.48             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.19/0.48  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t92_xboole_1, axiom,
% 0.19/0.48    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.48  thf('1', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ X12) = (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.19/0.48  thf(t93_xboole_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( k2_xboole_0 @ A @ B ) =
% 0.19/0.48       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      (![X13 : $i, X14 : $i]:
% 0.19/0.48         ((k2_xboole_0 @ X13 @ X14)
% 0.19/0.48           = (k2_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ 
% 0.19/0.48              (k3_xboole_0 @ X13 @ X14)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t93_xboole_1])).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((k2_xboole_0 @ X0 @ X0)
% 0.19/0.48           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ X0)))),
% 0.19/0.48      inference('sup+', [status(thm)], ['1', '2'])).
% 0.19/0.48  thf(idempotence_k2_xboole_0, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.19/0.48  thf('4', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.19/0.48      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.19/0.48  thf(idempotence_k3_xboole_0, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.19/0.48  thf('5', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.19/0.48      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.19/0.48  thf('6', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.19/0.48      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.19/0.48  thf('7', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t7_xboole_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 0.19/0.48      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.19/0.48  thf('9', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.19/0.48      inference('sup+', [status(thm)], ['7', '8'])).
% 0.19/0.48  thf(l3_zfmisc_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.19/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      (![X45 : $i, X46 : $i]:
% 0.19/0.48         (((X46) = (k1_tarski @ X45))
% 0.19/0.48          | ((X46) = (k1_xboole_0))
% 0.19/0.48          | ~ (r1_tarski @ X46 @ (k1_tarski @ X45)))),
% 0.19/0.48      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.48  thf('12', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t95_xboole_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( k3_xboole_0 @ A @ B ) =
% 0.19/0.48       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      (![X15 : $i, X16 : $i]:
% 0.19/0.48         ((k3_xboole_0 @ X15 @ X16)
% 0.19/0.48           = (k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ 
% 0.19/0.48              (k2_xboole_0 @ X15 @ X16)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.19/0.48  thf(t91_xboole_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.19/0.48       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.48         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 0.19/0.48           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (![X15 : $i, X16 : $i]:
% 0.19/0.48         ((k3_xboole_0 @ X15 @ X16)
% 0.19/0.48           = (k5_xboole_0 @ X15 @ 
% 0.19/0.48              (k5_xboole_0 @ X16 @ (k2_xboole_0 @ X15 @ X16))))),
% 0.19/0.48      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      (((k3_xboole_0 @ sk_B @ sk_C)
% 0.19/0.48         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C @ (k1_tarski @ sk_A))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['12', '15'])).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      ((((k3_xboole_0 @ sk_B @ sk_C)
% 0.19/0.48          = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C @ sk_B)))
% 0.19/0.48        | ((sk_B) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup+', [status(thm)], ['11', '16'])).
% 0.19/0.48  thf(commutativity_k5_xboole_0, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.19/0.48  thf('19', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ X12) = (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.48         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 0.19/0.48           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.19/0.48           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.19/0.48      inference('sup+', [status(thm)], ['19', '20'])).
% 0.19/0.48  thf('22', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.19/0.48  thf(t5_boole, axiom,
% 0.19/0.48    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.48  thf('23', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.19/0.48      inference('cnf', [status(esa)], [t5_boole])).
% 0.19/0.48  thf('24', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.19/0.48      inference('sup+', [status(thm)], ['22', '23'])).
% 0.19/0.48  thf('25', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['21', '24'])).
% 0.19/0.48  thf('26', plain,
% 0.19/0.48      ((((k3_xboole_0 @ sk_B @ sk_C) = (sk_C)) | ((sk_B) = (k1_xboole_0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['17', '18', '25'])).
% 0.19/0.48  thf(t17_xboole_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.19/0.48  thf('27', plain,
% 0.19/0.48      (![X4 : $i, X5 : $i]: (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ X4)),
% 0.19/0.48      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.19/0.48  thf('28', plain, (((r1_tarski @ sk_C @ sk_B) | ((sk_B) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup+', [status(thm)], ['26', '27'])).
% 0.19/0.48  thf('29', plain,
% 0.19/0.48      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.48  thf('30', plain,
% 0.19/0.48      (![X45 : $i, X46 : $i]:
% 0.19/0.48         (((X46) = (k1_tarski @ X45))
% 0.19/0.48          | ((X46) = (k1_xboole_0))
% 0.19/0.48          | ~ (r1_tarski @ X46 @ (k1_tarski @ X45)))),
% 0.19/0.48      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.19/0.48  thf('31', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (r1_tarski @ X0 @ sk_B)
% 0.19/0.48          | ((sk_B) = (k1_xboole_0))
% 0.19/0.48          | ((X0) = (k1_xboole_0))
% 0.19/0.48          | ((X0) = (k1_tarski @ sk_A)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.48  thf('32', plain,
% 0.19/0.48      ((((sk_B) = (k1_xboole_0))
% 0.19/0.48        | ((sk_C) = (k1_tarski @ sk_A))
% 0.19/0.48        | ((sk_C) = (k1_xboole_0))
% 0.19/0.48        | ((sk_B) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['28', '31'])).
% 0.19/0.48  thf('33', plain,
% 0.19/0.48      ((((sk_C) = (k1_xboole_0))
% 0.19/0.48        | ((sk_C) = (k1_tarski @ sk_A))
% 0.19/0.48        | ((sk_B) = (k1_xboole_0)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['32'])).
% 0.19/0.48  thf('34', plain,
% 0.19/0.48      ((((sk_B) != (k1_xboole_0)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('35', plain,
% 0.19/0.48      ((((sk_C) != (k1_tarski @ sk_A))) <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 0.19/0.48      inference('split', [status(esa)], ['34'])).
% 0.19/0.48  thf('36', plain,
% 0.19/0.48      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.19/0.48      inference('split', [status(esa)], ['34'])).
% 0.19/0.48  thf('37', plain,
% 0.19/0.48      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('38', plain,
% 0.19/0.48      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.19/0.48      inference('split', [status(esa)], ['37'])).
% 0.19/0.48  thf('39', plain,
% 0.19/0.48      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.48  thf('40', plain,
% 0.19/0.48      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('41', plain,
% 0.19/0.48      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.19/0.48      inference('split', [status(esa)], ['40'])).
% 0.19/0.48  thf('42', plain,
% 0.19/0.48      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.19/0.48         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['39', '41'])).
% 0.19/0.48  thf('43', plain,
% 0.19/0.48      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.19/0.48      inference('simplify', [status(thm)], ['42'])).
% 0.19/0.48  thf('44', plain,
% 0.19/0.48      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.19/0.48      inference('split', [status(esa)], ['34'])).
% 0.19/0.48  thf('45', plain,
% 0.19/0.48      ((((sk_B) != (sk_B)))
% 0.19/0.48         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['43', '44'])).
% 0.19/0.48  thf('46', plain,
% 0.19/0.48      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['45'])).
% 0.19/0.48  thf('47', plain, (~ (((sk_C) = (k1_tarski @ sk_A)))),
% 0.19/0.48      inference('sat_resolution*', [status(thm)], ['36', '38', '46'])).
% 0.19/0.48  thf('48', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['35', '47'])).
% 0.19/0.48  thf('49', plain,
% 0.19/0.48      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.19/0.48      inference('split', [status(esa)], ['40'])).
% 0.19/0.48  thf('50', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('51', plain,
% 0.19/0.48      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.19/0.48      inference('simplify', [status(thm)], ['42'])).
% 0.19/0.48  thf('52', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.19/0.48      inference('cnf', [status(esa)], [t5_boole])).
% 0.19/0.48  thf('53', plain,
% 0.19/0.48      ((![X0 : $i]: ((k5_xboole_0 @ X0 @ sk_B) = (X0)))
% 0.19/0.48         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['51', '52'])).
% 0.19/0.48  thf('54', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['21', '24'])).
% 0.19/0.48  thf('55', plain,
% 0.19/0.48      ((![X0 : $i]: ((sk_B) = (k5_xboole_0 @ X0 @ X0)))
% 0.19/0.48         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['53', '54'])).
% 0.19/0.48  thf('56', plain,
% 0.19/0.48      (![X13 : $i, X14 : $i]:
% 0.19/0.48         ((k2_xboole_0 @ X13 @ X14)
% 0.19/0.48           = (k2_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ 
% 0.19/0.48              (k3_xboole_0 @ X13 @ X14)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t93_xboole_1])).
% 0.19/0.48  thf('57', plain,
% 0.19/0.48      ((![X0 : $i]:
% 0.19/0.48          ((k2_xboole_0 @ X0 @ X0)
% 0.19/0.48            = (k2_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ X0))))
% 0.19/0.48         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['55', '56'])).
% 0.19/0.48  thf('58', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.19/0.48      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.19/0.48  thf('59', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.19/0.48      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.19/0.48  thf('60', plain,
% 0.19/0.48      ((![X0 : $i]: ((X0) = (k2_xboole_0 @ sk_B @ X0)))
% 0.19/0.48         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.19/0.48      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.19/0.48  thf('61', plain,
% 0.19/0.48      ((((sk_C) = (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['50', '60'])).
% 0.19/0.48  thf('62', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['35', '47'])).
% 0.19/0.48  thf('63', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['61', '62'])).
% 0.19/0.48  thf('64', plain,
% 0.19/0.48      (~ (((sk_C) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.19/0.48      inference('split', [status(esa)], ['40'])).
% 0.19/0.48  thf('65', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 0.19/0.48      inference('sat_resolution*', [status(thm)], ['63', '64'])).
% 0.19/0.48  thf('66', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['49', '65'])).
% 0.19/0.48  thf('67', plain, (((sk_B) = (k1_xboole_0))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['33', '48', '66'])).
% 0.19/0.48  thf('68', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ sk_B @ X0))),
% 0.19/0.48      inference('demod', [status(thm)], ['6', '67'])).
% 0.19/0.48  thf('69', plain, (((k1_tarski @ sk_A) = (sk_C))),
% 0.19/0.48      inference('demod', [status(thm)], ['0', '68'])).
% 0.19/0.48  thf('70', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['35', '47'])).
% 0.19/0.48  thf('71', plain, ($false),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['69', '70'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
