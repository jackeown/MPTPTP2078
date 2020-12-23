%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.b0igsgRoNm

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 311 expanded)
%              Number of leaves         :   23 ( 110 expanded)
%              Depth                    :   16
%              Number of atoms          :  585 (2261 expanded)
%              Number of equality atoms :  110 ( 376 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X21 @ ( k1_tarski @ X22 ) )
        = X21 )
      | ( r2_hidden @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('6',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('13',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','14'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('16',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X18 != X17 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X18 ) @ ( k1_tarski @ X17 ) )
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('17',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X17 ) @ ( k1_tarski @ X17 ) )
     != ( k1_tarski @ X17 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('20',plain,(
    ! [X17: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X17 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['15','20'])).

thf(t20_mcart_1,conjecture,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ? [B: $i,C: $i] :
            ( A
            = ( k4_tarski @ B @ C ) )
       => ( ( A
           != ( k1_mcart_1 @ A ) )
          & ( A
           != ( k2_mcart_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_mcart_1])).

thf('22',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('23',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X25 @ X26 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('24',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,
    ( ( sk_A = sk_B_1 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['24','26'])).

thf('28',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('30',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X28 = k1_xboole_0 )
      | ~ ( r2_hidden @ X30 @ X28 )
      | ( ( sk_B @ X28 )
       != ( k4_tarski @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_A ) )
       != sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','31'])).

thf('33',plain,(
    ! [X28: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X28 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('34',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X18 ) @ ( k1_tarski @ X19 ) )
        = ( k1_tarski @ X18 ) )
      | ( X18 = X19 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('35',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ( ( k4_xboole_0 @ X21 @ ( k1_tarski @ X20 ) )
       != X21 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( X0 = X1 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( sk_B @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['33','37'])).

thf('39',plain,(
    ! [X17: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X17 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('40',plain,(
    ! [X0: $i] :
      ( X0
      = ( sk_B @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( sk_A != sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','40'])).

thf('42',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['15','20'])).

thf('44',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X25: $i,X27: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X25 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('46',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['25'])).

thf('48',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X28 = k1_xboole_0 )
      | ~ ( r2_hidden @ X29 @ X28 )
      | ( ( sk_B @ X28 )
       != ( k4_tarski @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_A ) )
       != sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( X0
      = ( sk_B @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('55',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( sk_A != sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X17: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X17 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('58',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['25'])).

thf('61',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['42','61'])).

thf('63',plain,(
    ! [X17: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X17 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('64',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    $false ),
    inference(simplify,[status(thm)],['64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.b0igsgRoNm
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 21:03:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 159 iterations in 0.045s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.49  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.49  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(idempotence_k3_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.49  thf('0', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.20/0.49  thf(t100_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ X1 @ X2)
% 0.20/0.49           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['0', '1'])).
% 0.20/0.49  thf(t65_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.20/0.49       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X21 : $i, X22 : $i]:
% 0.20/0.49         (((k4_xboole_0 @ X21 @ (k1_tarski @ X22)) = (X21))
% 0.20/0.49          | (r2_hidden @ X22 @ X21))),
% 0.20/0.49      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.20/0.49            = (k1_tarski @ X0))
% 0.20/0.49          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf(t2_boole, axiom,
% 0.20/0.49    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ X1 @ X2)
% 0.20/0.49           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf(t5_boole, axiom,
% 0.20/0.49    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.49  thf('8', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.49  thf('9', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf(t48_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.20/0.49           = (k3_xboole_0 @ X4 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['0', '1'])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.49  thf('14', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_xboole_0) = (k1_tarski @ X0))
% 0.20/0.49          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['4', '14'])).
% 0.20/0.49  thf(t20_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.49         ( k1_tarski @ A ) ) <=>
% 0.20/0.49       ( ( A ) != ( B ) ) ))).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X17 : $i, X18 : $i]:
% 0.20/0.49         (((X18) != (X17))
% 0.20/0.49          | ((k4_xboole_0 @ (k1_tarski @ X18) @ (k1_tarski @ X17))
% 0.20/0.49              != (k1_tarski @ X18)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X17 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ (k1_tarski @ X17) @ (k1_tarski @ X17))
% 0.20/0.49           != (k1_tarski @ X17))),
% 0.20/0.49      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['0', '1'])).
% 0.20/0.49  thf('19', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.20/0.49  thf('20', plain, (![X17 : $i]: ((k1_xboole_0) != (k1_tarski @ X17))),
% 0.20/0.49      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.20/0.49  thf('21', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.49      inference('clc', [status(thm)], ['15', '20'])).
% 0.20/0.49  thf(t20_mcart_1, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.20/0.49       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.20/0.49          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.20/0.49  thf('22', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t7_mcart_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.49       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X25 : $i, X26 : $i]: ((k1_mcart_1 @ (k4_tarski @ X25 @ X26)) = (X25))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.49  thf('24', plain, (((k1_mcart_1 @ sk_A) = (sk_B_1))),
% 0.20/0.49      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.49      inference('split', [status(esa)], ['25'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      ((((sk_A) = (sk_B_1))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['24', '26'])).
% 0.20/0.49  thf('28', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.20/0.49         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['27', '28'])).
% 0.20/0.49  thf(t9_mcart_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ~( ( r2_hidden @ B @ A ) & 
% 0.20/0.49                 ( ![C:$i,D:$i]:
% 0.20/0.49                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.20/0.49                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.49         (((X28) = (k1_xboole_0))
% 0.20/0.49          | ~ (r2_hidden @ X30 @ X28)
% 0.20/0.49          | ((sk_B @ X28) != (k4_tarski @ X30 @ X29)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          (((sk_B @ X0) != (sk_A))
% 0.20/0.49           | ~ (r2_hidden @ sk_A @ X0)
% 0.20/0.49           | ((X0) = (k1_xboole_0))))
% 0.20/0.49         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.20/0.49         | ((sk_B @ (k1_tarski @ sk_A)) != (sk_A))))
% 0.20/0.49         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['21', '31'])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (![X28 : $i]:
% 0.20/0.49         (((X28) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X28) @ X28))),
% 0.20/0.49      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (![X18 : $i, X19 : $i]:
% 0.20/0.49         (((k4_xboole_0 @ (k1_tarski @ X18) @ (k1_tarski @ X19))
% 0.20/0.49            = (k1_tarski @ X18))
% 0.20/0.49          | ((X18) = (X19)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X20 : $i, X21 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X20 @ X21)
% 0.20/0.49          | ((k4_xboole_0 @ X21 @ (k1_tarski @ X20)) != (X21)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.20/0.49          | ((X0) = (X1))
% 0.20/0.49          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.20/0.49          | ((X0) = (sk_B @ (k1_tarski @ X0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['33', '37'])).
% 0.20/0.49  thf('39', plain, (![X17 : $i]: ((k1_xboole_0) != (k1_tarski @ X17))),
% 0.20/0.49      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.20/0.49  thf('40', plain, (![X0 : $i]: ((X0) = (sk_B @ (k1_tarski @ X0)))),
% 0.20/0.49      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      (((((k1_tarski @ sk_A) = (k1_xboole_0)) | ((sk_A) != (sk_A))))
% 0.20/0.49         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.49      inference('demod', [status(thm)], ['32', '40'])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.20/0.49         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.49  thf('43', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.49      inference('clc', [status(thm)], ['15', '20'])).
% 0.20/0.49  thf('44', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      (![X25 : $i, X27 : $i]: ((k2_mcart_1 @ (k4_tarski @ X25 @ X27)) = (X27))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.49  thf('46', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.20/0.49      inference('sup+', [status(thm)], ['44', '45'])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.49      inference('split', [status(esa)], ['25'])).
% 0.20/0.49  thf('48', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['46', '47'])).
% 0.20/0.49  thf('49', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('50', plain,
% 0.20/0.49      ((((sk_A) = (k4_tarski @ sk_B_1 @ sk_A)))
% 0.20/0.49         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['48', '49'])).
% 0.20/0.49  thf('51', plain,
% 0.20/0.49      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.49         (((X28) = (k1_xboole_0))
% 0.20/0.49          | ~ (r2_hidden @ X29 @ X28)
% 0.20/0.49          | ((sk_B @ X28) != (k4_tarski @ X30 @ X29)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.20/0.49  thf('52', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          (((sk_B @ X0) != (sk_A))
% 0.20/0.49           | ~ (r2_hidden @ sk_A @ X0)
% 0.20/0.49           | ((X0) = (k1_xboole_0))))
% 0.20/0.49         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.20/0.49         | ((sk_B @ (k1_tarski @ sk_A)) != (sk_A))))
% 0.20/0.49         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['43', '52'])).
% 0.20/0.49  thf('54', plain, (![X0 : $i]: ((X0) = (sk_B @ (k1_tarski @ X0)))),
% 0.20/0.49      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.49  thf('55', plain,
% 0.20/0.49      (((((k1_tarski @ sk_A) = (k1_xboole_0)) | ((sk_A) != (sk_A))))
% 0.20/0.49         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.49      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.49  thf('56', plain,
% 0.20/0.49      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.20/0.49         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['55'])).
% 0.20/0.49  thf('57', plain, (![X17 : $i]: ((k1_xboole_0) != (k1_tarski @ X17))),
% 0.20/0.49      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.20/0.49  thf('58', plain,
% 0.20/0.49      ((((k1_xboole_0) != (k1_xboole_0))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.49  thf('59', plain, (~ (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['58'])).
% 0.20/0.49  thf('60', plain,
% 0.20/0.49      ((((sk_A) = (k1_mcart_1 @ sk_A))) | (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.20/0.49      inference('split', [status(esa)], ['25'])).
% 0.20/0.49  thf('61', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['59', '60'])).
% 0.20/0.49  thf('62', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['42', '61'])).
% 0.20/0.49  thf('63', plain, (![X17 : $i]: ((k1_xboole_0) != (k1_tarski @ X17))),
% 0.20/0.49      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.20/0.49  thf('64', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.49  thf('65', plain, ($false), inference('simplify', [status(thm)], ['64'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
