%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sAE64KKR67

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:20 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 445 expanded)
%              Number of leaves         :   19 ( 117 expanded)
%              Depth                    :   19
%              Number of atoms          :  576 (5504 expanded)
%              Number of equality atoms :  122 (1286 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X23
        = ( k1_tarski @ X22 ) )
      | ( X23 = k1_xboole_0 )
      | ~ ( r1_tarski @ X23 @ ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('7',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_C
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('11',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('15',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X23
        = ( k1_tarski @ X22 ) )
      | ( X23 = k1_xboole_0 )
      | ~ ( r1_tarski @ X23 @ ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('17',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('23',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['10','12','24'])).

thf('26',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['9','25'])).

thf('27',plain,(
    sk_C = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','26'])).

thf('28',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('29',plain,
    ( ( sk_B = sk_C )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    sk_C = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','26'])).

thf('31',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('32',plain,
    ( ( sk_C != sk_C )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('35',plain,(
    sk_B
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['33','34'])).

thf('36',plain,(
    sk_B = sk_C ),
    inference(simpl_trail,[status(thm)],['29','35'])).

thf('37',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['0','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('39',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ X8 )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('43',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ X0 @ sk_B )
        = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ X0 @ sk_B )
        = sk_B )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('47',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ sk_B )
        = ( k5_xboole_0 @ X0 @ sk_B ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('50',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ X0 @ sk_B )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ sk_B )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,(
    sk_B
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['33','34'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ sk_B )
      = X0 ) ),
    inference(simpl_trail,[status(thm)],['52','53'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('55',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ X0 @ sk_B )
        = sk_B )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_B @ X0 )
        = sk_B )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_B @ X0 )
        = ( k5_xboole_0 @ sk_B @ sk_B ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ X0 @ sk_B )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    sk_B
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['33','34'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = sk_B ) ),
    inference(simpl_trail,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['41','54','63'])).

thf('65',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['18'])).

thf('66',plain,(
    sk_B
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['33','34'])).

thf('67',plain,(
    sk_B
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['65','66'])).

thf('68',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['64','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sAE64KKR67
% 0.17/0.36  % Computer   : n009.cluster.edu
% 0.17/0.36  % Model      : x86_64 x86_64
% 0.17/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.36  % Memory     : 8042.1875MB
% 0.17/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.36  % CPULimit   : 60
% 0.17/0.36  % DateTime   : Tue Dec  1 18:56:41 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.37  % Running portfolio for 600 s
% 0.17/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.37  % Number of cores: 8
% 0.17/0.37  % Python version: Python 3.6.8
% 0.17/0.37  % Running in FO mode
% 0.24/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.51  % Solved by: fo/fo7.sh
% 0.24/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.51  % done 78 iterations in 0.027s
% 0.24/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.51  % SZS output start Refutation
% 0.24/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.24/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.24/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.51  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.24/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.51  thf(t43_zfmisc_1, conjecture,
% 0.24/0.51    (![A:$i,B:$i,C:$i]:
% 0.24/0.51     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.24/0.51          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.24/0.51          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.24/0.51          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.24/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.24/0.51        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.24/0.51             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.24/0.51             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.24/0.51             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.24/0.51    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.24/0.51  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf(commutativity_k2_xboole_0, axiom,
% 0.24/0.51    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.24/0.51  thf('2', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.24/0.51      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.24/0.51  thf(t7_xboole_1, axiom,
% 0.24/0.51    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.24/0.51  thf('3', plain,
% 0.24/0.51      (![X10 : $i, X11 : $i]: (r1_tarski @ X10 @ (k2_xboole_0 @ X10 @ X11))),
% 0.24/0.51      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.24/0.51  thf('4', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.24/0.51      inference('sup+', [status(thm)], ['2', '3'])).
% 0.24/0.51  thf('5', plain, ((r1_tarski @ sk_C @ (k1_tarski @ sk_A))),
% 0.24/0.51      inference('sup+', [status(thm)], ['1', '4'])).
% 0.24/0.51  thf(l3_zfmisc_1, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.24/0.51       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.24/0.51  thf('6', plain,
% 0.24/0.51      (![X22 : $i, X23 : $i]:
% 0.24/0.51         (((X23) = (k1_tarski @ X22))
% 0.24/0.51          | ((X23) = (k1_xboole_0))
% 0.24/0.51          | ~ (r1_tarski @ X23 @ (k1_tarski @ X22)))),
% 0.24/0.51      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.24/0.51  thf('7', plain, ((((sk_C) = (k1_xboole_0)) | ((sk_C) = (k1_tarski @ sk_A)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.24/0.51  thf('8', plain,
% 0.24/0.51      ((((sk_B) != (k1_xboole_0)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('9', plain,
% 0.24/0.51      ((((sk_C) != (k1_tarski @ sk_A))) <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 0.24/0.51      inference('split', [status(esa)], ['8'])).
% 0.24/0.51  thf('10', plain,
% 0.24/0.51      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.24/0.51      inference('split', [status(esa)], ['8'])).
% 0.24/0.51  thf('11', plain,
% 0.24/0.51      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('12', plain,
% 0.24/0.51      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.24/0.51      inference('split', [status(esa)], ['11'])).
% 0.24/0.51  thf('13', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('14', plain,
% 0.24/0.51      (![X10 : $i, X11 : $i]: (r1_tarski @ X10 @ (k2_xboole_0 @ X10 @ X11))),
% 0.24/0.51      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.24/0.51  thf('15', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.24/0.51      inference('sup+', [status(thm)], ['13', '14'])).
% 0.24/0.51  thf('16', plain,
% 0.24/0.51      (![X22 : $i, X23 : $i]:
% 0.24/0.51         (((X23) = (k1_tarski @ X22))
% 0.24/0.51          | ((X23) = (k1_xboole_0))
% 0.24/0.51          | ~ (r1_tarski @ X23 @ (k1_tarski @ X22)))),
% 0.24/0.51      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.24/0.51  thf('17', plain,
% 0.24/0.51      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.24/0.51  thf('18', plain,
% 0.24/0.51      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_xboole_0)))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('19', plain,
% 0.24/0.51      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.24/0.51      inference('split', [status(esa)], ['18'])).
% 0.24/0.51  thf('20', plain,
% 0.24/0.51      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.24/0.51         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.24/0.51      inference('sup-', [status(thm)], ['17', '19'])).
% 0.24/0.51  thf('21', plain,
% 0.24/0.51      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.24/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.24/0.51  thf('22', plain,
% 0.24/0.51      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.24/0.51      inference('split', [status(esa)], ['8'])).
% 0.24/0.51  thf('23', plain,
% 0.24/0.51      ((((sk_B) != (sk_B)))
% 0.24/0.51         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.24/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.24/0.51  thf('24', plain,
% 0.24/0.51      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.24/0.51      inference('simplify', [status(thm)], ['23'])).
% 0.24/0.51  thf('25', plain, (~ (((sk_C) = (k1_tarski @ sk_A)))),
% 0.24/0.51      inference('sat_resolution*', [status(thm)], ['10', '12', '24'])).
% 0.24/0.51  thf('26', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.24/0.51      inference('simpl_trail', [status(thm)], ['9', '25'])).
% 0.24/0.51  thf('27', plain, (((sk_C) = (k1_xboole_0))),
% 0.24/0.51      inference('simplify_reflect-', [status(thm)], ['7', '26'])).
% 0.24/0.51  thf('28', plain,
% 0.24/0.51      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.24/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.24/0.51  thf('29', plain,
% 0.24/0.51      ((((sk_B) = (sk_C))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.24/0.51      inference('sup+', [status(thm)], ['27', '28'])).
% 0.24/0.51  thf('30', plain, (((sk_C) = (k1_xboole_0))),
% 0.24/0.51      inference('simplify_reflect-', [status(thm)], ['7', '26'])).
% 0.24/0.51  thf('31', plain,
% 0.24/0.51      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.24/0.51      inference('split', [status(esa)], ['18'])).
% 0.24/0.51  thf('32', plain, ((((sk_C) != (sk_C))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.24/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.24/0.51  thf('33', plain, ((((sk_C) = (k1_xboole_0)))),
% 0.24/0.51      inference('simplify', [status(thm)], ['32'])).
% 0.24/0.51  thf('34', plain,
% 0.24/0.51      (~ (((sk_B) = (k1_tarski @ sk_A))) | ~ (((sk_C) = (k1_xboole_0)))),
% 0.24/0.51      inference('split', [status(esa)], ['18'])).
% 0.24/0.51  thf('35', plain, (~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.24/0.51      inference('sat_resolution*', [status(thm)], ['33', '34'])).
% 0.24/0.51  thf('36', plain, (((sk_B) = (sk_C))),
% 0.24/0.51      inference('simpl_trail', [status(thm)], ['29', '35'])).
% 0.24/0.51  thf('37', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_B))),
% 0.24/0.51      inference('demod', [status(thm)], ['0', '36'])).
% 0.24/0.51  thf('38', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.24/0.51      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.24/0.51  thf(t40_xboole_1, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.24/0.51  thf('39', plain,
% 0.24/0.51      (![X7 : $i, X8 : $i]:
% 0.24/0.51         ((k4_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ X8)
% 0.24/0.51           = (k4_xboole_0 @ X7 @ X8))),
% 0.24/0.51      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.24/0.51  thf('40', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.24/0.51           = (k4_xboole_0 @ X0 @ X1))),
% 0.24/0.51      inference('sup+', [status(thm)], ['38', '39'])).
% 0.24/0.51  thf('41', plain,
% 0.24/0.51      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k4_xboole_0 @ sk_B @ sk_B))),
% 0.24/0.51      inference('sup+', [status(thm)], ['37', '40'])).
% 0.24/0.51  thf('42', plain,
% 0.24/0.51      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.24/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.24/0.51  thf(t2_boole, axiom,
% 0.24/0.51    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.24/0.51  thf('43', plain,
% 0.24/0.51      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.24/0.51      inference('cnf', [status(esa)], [t2_boole])).
% 0.24/0.51  thf('44', plain,
% 0.24/0.51      ((![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_B) = (k1_xboole_0)))
% 0.24/0.51         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.24/0.51      inference('sup+', [status(thm)], ['42', '43'])).
% 0.24/0.51  thf('45', plain,
% 0.24/0.51      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.24/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.24/0.51  thf('46', plain,
% 0.24/0.51      ((![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_B) = (sk_B)))
% 0.24/0.51         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.24/0.51      inference('demod', [status(thm)], ['44', '45'])).
% 0.24/0.51  thf(t100_xboole_1, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.24/0.51  thf('47', plain,
% 0.24/0.51      (![X4 : $i, X5 : $i]:
% 0.24/0.51         ((k4_xboole_0 @ X4 @ X5)
% 0.24/0.51           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.24/0.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.24/0.51  thf('48', plain,
% 0.24/0.51      ((![X0 : $i]: ((k4_xboole_0 @ X0 @ sk_B) = (k5_xboole_0 @ X0 @ sk_B)))
% 0.24/0.51         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.24/0.51      inference('sup+', [status(thm)], ['46', '47'])).
% 0.24/0.51  thf('49', plain,
% 0.24/0.51      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.24/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.24/0.51  thf(t5_boole, axiom,
% 0.24/0.51    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.24/0.51  thf('50', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.24/0.51      inference('cnf', [status(esa)], [t5_boole])).
% 0.24/0.51  thf('51', plain,
% 0.24/0.51      ((![X0 : $i]: ((k5_xboole_0 @ X0 @ sk_B) = (X0)))
% 0.24/0.51         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.24/0.51      inference('sup+', [status(thm)], ['49', '50'])).
% 0.24/0.51  thf('52', plain,
% 0.24/0.51      ((![X0 : $i]: ((k4_xboole_0 @ X0 @ sk_B) = (X0)))
% 0.24/0.51         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.24/0.51      inference('demod', [status(thm)], ['48', '51'])).
% 0.24/0.51  thf('53', plain, (~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.24/0.51      inference('sat_resolution*', [status(thm)], ['33', '34'])).
% 0.24/0.51  thf('54', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ sk_B) = (X0))),
% 0.24/0.51      inference('simpl_trail', [status(thm)], ['52', '53'])).
% 0.24/0.51  thf(commutativity_k3_xboole_0, axiom,
% 0.24/0.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.24/0.51  thf('55', plain,
% 0.24/0.51      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.24/0.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.24/0.51  thf('56', plain,
% 0.24/0.51      ((![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_B) = (sk_B)))
% 0.24/0.51         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.24/0.51      inference('demod', [status(thm)], ['44', '45'])).
% 0.24/0.51  thf('57', plain,
% 0.24/0.51      ((![X0 : $i]: ((k3_xboole_0 @ sk_B @ X0) = (sk_B)))
% 0.24/0.51         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.24/0.51      inference('sup+', [status(thm)], ['55', '56'])).
% 0.24/0.51  thf('58', plain,
% 0.24/0.51      (![X4 : $i, X5 : $i]:
% 0.24/0.51         ((k4_xboole_0 @ X4 @ X5)
% 0.24/0.51           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.24/0.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.24/0.51  thf('59', plain,
% 0.24/0.51      ((![X0 : $i]: ((k4_xboole_0 @ sk_B @ X0) = (k5_xboole_0 @ sk_B @ sk_B)))
% 0.24/0.51         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.24/0.51      inference('sup+', [status(thm)], ['57', '58'])).
% 0.24/0.51  thf('60', plain,
% 0.24/0.51      ((![X0 : $i]: ((k5_xboole_0 @ X0 @ sk_B) = (X0)))
% 0.24/0.51         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.24/0.51      inference('sup+', [status(thm)], ['49', '50'])).
% 0.24/0.51  thf('61', plain,
% 0.24/0.51      ((![X0 : $i]: ((k4_xboole_0 @ sk_B @ X0) = (sk_B)))
% 0.24/0.51         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.24/0.51      inference('demod', [status(thm)], ['59', '60'])).
% 0.24/0.51  thf('62', plain, (~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.24/0.51      inference('sat_resolution*', [status(thm)], ['33', '34'])).
% 0.24/0.51  thf('63', plain, (![X0 : $i]: ((k4_xboole_0 @ sk_B @ X0) = (sk_B))),
% 0.24/0.51      inference('simpl_trail', [status(thm)], ['61', '62'])).
% 0.24/0.51  thf('64', plain, (((k1_tarski @ sk_A) = (sk_B))),
% 0.24/0.51      inference('demod', [status(thm)], ['41', '54', '63'])).
% 0.24/0.51  thf('65', plain,
% 0.24/0.51      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.24/0.51      inference('split', [status(esa)], ['18'])).
% 0.24/0.51  thf('66', plain, (~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.24/0.51      inference('sat_resolution*', [status(thm)], ['33', '34'])).
% 0.24/0.51  thf('67', plain, (((sk_B) != (k1_tarski @ sk_A))),
% 0.24/0.51      inference('simpl_trail', [status(thm)], ['65', '66'])).
% 0.24/0.51  thf('68', plain, ($false),
% 0.24/0.51      inference('simplify_reflect-', [status(thm)], ['64', '67'])).
% 0.24/0.51  
% 0.24/0.51  % SZS output end Refutation
% 0.24/0.51  
% 0.24/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
