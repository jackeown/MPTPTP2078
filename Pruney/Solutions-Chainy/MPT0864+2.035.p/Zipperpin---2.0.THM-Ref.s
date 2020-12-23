%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3FMt59DgM2

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:04 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 296 expanded)
%              Number of leaves         :   25 (  93 expanded)
%              Depth                    :   24
%              Number of atoms          :  669 (2655 expanded)
%              Number of equality atoms :  124 ( 501 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf('0',plain,(
    ! [X51: $i] :
      ( ( X51 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X51 ) @ X51 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( X9 = X6 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9 = X6 )
      | ~ ( r2_hidden @ X9 @ ( k1_tarski @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X7 != X6 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('5',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_tarski @ X6 ) ) ),
    inference(simplify,[status(thm)],['4'])).

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

thf('6',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('7',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X48 @ X49 ) )
      = X48 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('8',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ( sk_A = sk_B_1 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','10'])).

thf('12',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C_1 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X11: $i] :
      ( ( k2_tarski @ X11 @ X11 )
      = ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('15',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_tarski @ X6 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('16',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X48: $i,X50: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X48 @ X50 ) )
      = X50 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('18',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['9'])).

thf('20',plain,
    ( ( sk_A = sk_C_1 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( X51 = k1_xboole_0 )
      | ~ ( r2_hidden @ X52 @ X51 )
      | ( ( sk_B @ X51 )
       != ( k4_tarski @ X53 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_A ) )
       != sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('27',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('28',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X41 ) @ ( k2_tarski @ X41 @ X42 ) )
      = ( k1_tarski @ X41 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) )
        = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('37',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) )
        = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','38'])).

thf('40',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['14','39'])).

thf('41',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('42',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('44',plain,(
    ! [X43: $i,X44: $i] :
      ( ( X44 != X43 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X44 ) @ ( k1_tarski @ X43 ) )
       != ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('45',plain,(
    ! [X43: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X43 ) @ ( k1_tarski @ X43 ) )
     != ( k1_tarski @ X43 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
     != ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('48',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('49',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['42','49'])).

thf('51',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['9'])).

thf('52',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['50','51'])).

thf('53',plain,
    ( sk_A
    = ( k4_tarski @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['13','52'])).

thf('54',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( X51 = k1_xboole_0 )
      | ~ ( r2_hidden @ X53 @ X51 )
      | ( ( sk_B @ X51 )
       != ( k4_tarski @ X53 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != sk_A )
      | ~ ( r2_hidden @ sk_A @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( sk_B @ ( k1_tarski @ sk_A ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['5','55'])).

thf('57',plain,(
    ! [X11: $i] :
      ( ( k2_tarski @ X11 @ X11 )
      = ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('58',plain,(
    ! [X43: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X43 ) @ ( k1_tarski @ X43 ) )
     != ( k1_tarski @ X43 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) )
     != ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X41 ) @ ( k2_tarski @ X41 @ X42 ) )
      = ( k1_tarski @ X41 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['59','64'])).

thf('66',plain,(
    ( sk_B @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(clc,[status(thm)],['56','65'])).

thf('67',plain,
    ( ( sk_A != sk_A )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','66'])).

thf('68',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['59','64'])).

thf('70',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    $false ),
    inference(simplify,[status(thm)],['70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3FMt59DgM2
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:44:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.34/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.34/0.53  % Solved by: fo/fo7.sh
% 0.34/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.53  % done 248 iterations in 0.064s
% 0.34/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.34/0.53  % SZS output start Refutation
% 0.34/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.34/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.34/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.34/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.34/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.34/0.53  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.34/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.34/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.34/0.53  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.34/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.34/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.34/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.34/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.34/0.53  thf(t9_mcart_1, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.34/0.53          ( ![B:$i]:
% 0.34/0.53            ( ~( ( r2_hidden @ B @ A ) & 
% 0.34/0.53                 ( ![C:$i,D:$i]:
% 0.34/0.53                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.34/0.53                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.34/0.53  thf('0', plain,
% 0.34/0.53      (![X51 : $i]:
% 0.34/0.53         (((X51) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X51) @ X51))),
% 0.34/0.53      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.34/0.53  thf(d1_tarski, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.34/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.34/0.53  thf('1', plain,
% 0.34/0.53      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.34/0.53         (~ (r2_hidden @ X9 @ X8) | ((X9) = (X6)) | ((X8) != (k1_tarski @ X6)))),
% 0.34/0.53      inference('cnf', [status(esa)], [d1_tarski])).
% 0.34/0.53  thf('2', plain,
% 0.34/0.53      (![X6 : $i, X9 : $i]:
% 0.34/0.53         (((X9) = (X6)) | ~ (r2_hidden @ X9 @ (k1_tarski @ X6)))),
% 0.34/0.53      inference('simplify', [status(thm)], ['1'])).
% 0.34/0.53  thf('3', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.34/0.53          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['0', '2'])).
% 0.34/0.53  thf('4', plain,
% 0.34/0.53      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.34/0.53         (((X7) != (X6)) | (r2_hidden @ X7 @ X8) | ((X8) != (k1_tarski @ X6)))),
% 0.34/0.53      inference('cnf', [status(esa)], [d1_tarski])).
% 0.34/0.53  thf('5', plain, (![X6 : $i]: (r2_hidden @ X6 @ (k1_tarski @ X6))),
% 0.34/0.53      inference('simplify', [status(thm)], ['4'])).
% 0.34/0.53  thf(t20_mcart_1, conjecture,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.34/0.53       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.34/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.53    (~( ![A:$i]:
% 0.34/0.53        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.34/0.53          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.34/0.53    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.34/0.53  thf('6', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(t7_mcart_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.34/0.53       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.34/0.53  thf('7', plain,
% 0.34/0.53      (![X48 : $i, X49 : $i]: ((k1_mcart_1 @ (k4_tarski @ X48 @ X49)) = (X48))),
% 0.34/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.34/0.53  thf('8', plain, (((k1_mcart_1 @ sk_A) = (sk_B_1))),
% 0.34/0.53      inference('sup+', [status(thm)], ['6', '7'])).
% 0.34/0.53  thf('9', plain,
% 0.34/0.53      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('10', plain,
% 0.34/0.53      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.34/0.53      inference('split', [status(esa)], ['9'])).
% 0.34/0.53  thf('11', plain,
% 0.34/0.53      ((((sk_A) = (sk_B_1))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.34/0.53      inference('sup+', [status(thm)], ['8', '10'])).
% 0.34/0.53  thf('12', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('13', plain,
% 0.34/0.53      ((((sk_A) = (k4_tarski @ sk_A @ sk_C_1)))
% 0.34/0.53         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.34/0.53      inference('sup+', [status(thm)], ['11', '12'])).
% 0.34/0.53  thf(t69_enumset1, axiom,
% 0.34/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.34/0.53  thf('14', plain,
% 0.34/0.53      (![X11 : $i]: ((k2_tarski @ X11 @ X11) = (k1_tarski @ X11))),
% 0.34/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.34/0.53  thf('15', plain, (![X6 : $i]: (r2_hidden @ X6 @ (k1_tarski @ X6))),
% 0.34/0.53      inference('simplify', [status(thm)], ['4'])).
% 0.34/0.53  thf('16', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('17', plain,
% 0.34/0.53      (![X48 : $i, X50 : $i]: ((k2_mcart_1 @ (k4_tarski @ X48 @ X50)) = (X50))),
% 0.34/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.34/0.53  thf('18', plain, (((k2_mcart_1 @ sk_A) = (sk_C_1))),
% 0.34/0.53      inference('sup+', [status(thm)], ['16', '17'])).
% 0.34/0.53  thf('19', plain,
% 0.34/0.53      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.34/0.53      inference('split', [status(esa)], ['9'])).
% 0.34/0.53  thf('20', plain,
% 0.34/0.53      ((((sk_A) = (sk_C_1))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.34/0.53      inference('sup+', [status(thm)], ['18', '19'])).
% 0.34/0.53  thf('21', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('22', plain,
% 0.34/0.53      ((((sk_A) = (k4_tarski @ sk_B_1 @ sk_A)))
% 0.34/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.34/0.53      inference('sup+', [status(thm)], ['20', '21'])).
% 0.34/0.53  thf('23', plain,
% 0.34/0.53      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.34/0.53         (((X51) = (k1_xboole_0))
% 0.34/0.53          | ~ (r2_hidden @ X52 @ X51)
% 0.34/0.53          | ((sk_B @ X51) != (k4_tarski @ X53 @ X52)))),
% 0.34/0.53      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.34/0.53  thf('24', plain,
% 0.34/0.53      ((![X0 : $i]:
% 0.34/0.53          (((sk_B @ X0) != (sk_A))
% 0.34/0.53           | ~ (r2_hidden @ sk_A @ X0)
% 0.34/0.53           | ((X0) = (k1_xboole_0))))
% 0.34/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.34/0.53  thf('25', plain,
% 0.34/0.53      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.34/0.53         | ((sk_B @ (k1_tarski @ sk_A)) != (sk_A))))
% 0.34/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['15', '24'])).
% 0.34/0.53  thf('26', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.34/0.53          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['0', '2'])).
% 0.34/0.53  thf('27', plain,
% 0.34/0.53      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.34/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.34/0.53      inference('clc', [status(thm)], ['25', '26'])).
% 0.34/0.53  thf(t19_zfmisc_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.34/0.53       ( k1_tarski @ A ) ))).
% 0.34/0.53  thf('28', plain,
% 0.34/0.53      (![X41 : $i, X42 : $i]:
% 0.34/0.53         ((k3_xboole_0 @ (k1_tarski @ X41) @ (k2_tarski @ X41 @ X42))
% 0.34/0.53           = (k1_tarski @ X41))),
% 0.34/0.53      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.34/0.53  thf('29', plain,
% 0.34/0.53      ((![X0 : $i]:
% 0.34/0.53          ((k3_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ X0))
% 0.34/0.53            = (k1_tarski @ sk_A)))
% 0.34/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.34/0.53      inference('sup+', [status(thm)], ['27', '28'])).
% 0.34/0.53  thf('30', plain,
% 0.34/0.53      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.34/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.34/0.53      inference('clc', [status(thm)], ['25', '26'])).
% 0.34/0.53  thf('31', plain,
% 0.34/0.53      ((![X0 : $i]:
% 0.34/0.53          ((k3_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ X0))
% 0.34/0.53            = (k1_xboole_0)))
% 0.34/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.34/0.53      inference('demod', [status(thm)], ['29', '30'])).
% 0.34/0.53  thf(t100_xboole_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.34/0.53  thf('32', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         ((k4_xboole_0 @ X0 @ X1)
% 0.34/0.53           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.34/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.34/0.53  thf('33', plain,
% 0.34/0.53      ((![X0 : $i]:
% 0.34/0.53          ((k4_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ X0))
% 0.34/0.53            = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))
% 0.34/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.34/0.53      inference('sup+', [status(thm)], ['31', '32'])).
% 0.34/0.53  thf(t21_xboole_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.34/0.53  thf('34', plain,
% 0.34/0.53      (![X2 : $i, X3 : $i]:
% 0.34/0.53         ((k3_xboole_0 @ X2 @ (k2_xboole_0 @ X2 @ X3)) = (X2))),
% 0.34/0.53      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.34/0.53  thf('35', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         ((k4_xboole_0 @ X0 @ X1)
% 0.34/0.53           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.34/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.34/0.53  thf('36', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.34/0.53           = (k5_xboole_0 @ X0 @ X0))),
% 0.34/0.53      inference('sup+', [status(thm)], ['34', '35'])).
% 0.34/0.53  thf(t46_xboole_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.34/0.53  thf('37', plain,
% 0.34/0.53      (![X4 : $i, X5 : $i]:
% 0.34/0.53         ((k4_xboole_0 @ X4 @ (k2_xboole_0 @ X4 @ X5)) = (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.34/0.53  thf('38', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.34/0.53      inference('sup+', [status(thm)], ['36', '37'])).
% 0.34/0.53  thf('39', plain,
% 0.34/0.53      ((![X0 : $i]:
% 0.34/0.53          ((k4_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ X0))
% 0.34/0.53            = (k1_xboole_0)))
% 0.34/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.34/0.53      inference('demod', [status(thm)], ['33', '38'])).
% 0.34/0.53  thf('40', plain,
% 0.34/0.53      ((((k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 0.34/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.34/0.53      inference('sup+', [status(thm)], ['14', '39'])).
% 0.34/0.53  thf('41', plain,
% 0.34/0.53      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.34/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.34/0.53      inference('clc', [status(thm)], ['25', '26'])).
% 0.34/0.53  thf('42', plain,
% 0.34/0.53      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0)))
% 0.34/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.34/0.53      inference('demod', [status(thm)], ['40', '41'])).
% 0.34/0.53  thf('43', plain,
% 0.34/0.53      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.34/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.34/0.53      inference('clc', [status(thm)], ['25', '26'])).
% 0.34/0.53  thf(t20_zfmisc_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.34/0.53         ( k1_tarski @ A ) ) <=>
% 0.34/0.53       ( ( A ) != ( B ) ) ))).
% 0.34/0.53  thf('44', plain,
% 0.34/0.53      (![X43 : $i, X44 : $i]:
% 0.34/0.53         (((X44) != (X43))
% 0.34/0.53          | ((k4_xboole_0 @ (k1_tarski @ X44) @ (k1_tarski @ X43))
% 0.34/0.53              != (k1_tarski @ X44)))),
% 0.34/0.53      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.34/0.53  thf('45', plain,
% 0.34/0.53      (![X43 : $i]:
% 0.34/0.53         ((k4_xboole_0 @ (k1_tarski @ X43) @ (k1_tarski @ X43))
% 0.34/0.53           != (k1_tarski @ X43))),
% 0.34/0.53      inference('simplify', [status(thm)], ['44'])).
% 0.34/0.53  thf('46', plain,
% 0.34/0.53      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) != (k1_tarski @ sk_A)))
% 0.34/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['43', '45'])).
% 0.34/0.53  thf('47', plain,
% 0.34/0.53      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.34/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.34/0.53      inference('clc', [status(thm)], ['25', '26'])).
% 0.34/0.53  thf('48', plain,
% 0.34/0.53      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.34/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.34/0.53      inference('clc', [status(thm)], ['25', '26'])).
% 0.34/0.53  thf('49', plain,
% 0.34/0.53      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0)))
% 0.34/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.34/0.53      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.34/0.53  thf('50', plain, (~ (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.34/0.53      inference('simplify_reflect-', [status(thm)], ['42', '49'])).
% 0.34/0.53  thf('51', plain,
% 0.34/0.53      ((((sk_A) = (k1_mcart_1 @ sk_A))) | (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.34/0.53      inference('split', [status(esa)], ['9'])).
% 0.34/0.53  thf('52', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.34/0.53      inference('sat_resolution*', [status(thm)], ['50', '51'])).
% 0.34/0.53  thf('53', plain, (((sk_A) = (k4_tarski @ sk_A @ sk_C_1))),
% 0.34/0.53      inference('simpl_trail', [status(thm)], ['13', '52'])).
% 0.34/0.53  thf('54', plain,
% 0.34/0.53      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.34/0.53         (((X51) = (k1_xboole_0))
% 0.34/0.53          | ~ (r2_hidden @ X53 @ X51)
% 0.34/0.53          | ((sk_B @ X51) != (k4_tarski @ X53 @ X52)))),
% 0.34/0.53      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.34/0.53  thf('55', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (((sk_B @ X0) != (sk_A))
% 0.34/0.53          | ~ (r2_hidden @ sk_A @ X0)
% 0.34/0.53          | ((X0) = (k1_xboole_0)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['53', '54'])).
% 0.34/0.53  thf('56', plain,
% 0.34/0.53      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.34/0.53        | ((sk_B @ (k1_tarski @ sk_A)) != (sk_A)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['5', '55'])).
% 0.34/0.53  thf('57', plain,
% 0.34/0.53      (![X11 : $i]: ((k2_tarski @ X11 @ X11) = (k1_tarski @ X11))),
% 0.34/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.34/0.53  thf('58', plain,
% 0.34/0.53      (![X43 : $i]:
% 0.34/0.53         ((k4_xboole_0 @ (k1_tarski @ X43) @ (k1_tarski @ X43))
% 0.34/0.53           != (k1_tarski @ X43))),
% 0.34/0.53      inference('simplify', [status(thm)], ['44'])).
% 0.34/0.53  thf('59', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))
% 0.34/0.53           != (k1_tarski @ X0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['57', '58'])).
% 0.34/0.53  thf('60', plain,
% 0.34/0.53      (![X41 : $i, X42 : $i]:
% 0.34/0.53         ((k3_xboole_0 @ (k1_tarski @ X41) @ (k2_tarski @ X41 @ X42))
% 0.34/0.53           = (k1_tarski @ X41))),
% 0.34/0.53      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.34/0.53  thf('61', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         ((k4_xboole_0 @ X0 @ X1)
% 0.34/0.53           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.34/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.34/0.53  thf('62', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 0.34/0.53           = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.34/0.53      inference('sup+', [status(thm)], ['60', '61'])).
% 0.34/0.53  thf('63', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.34/0.53      inference('sup+', [status(thm)], ['36', '37'])).
% 0.34/0.53  thf('64', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 0.34/0.53           = (k1_xboole_0))),
% 0.34/0.53      inference('demod', [status(thm)], ['62', '63'])).
% 0.34/0.53  thf('65', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.34/0.53      inference('demod', [status(thm)], ['59', '64'])).
% 0.34/0.53  thf('66', plain, (((sk_B @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.34/0.53      inference('clc', [status(thm)], ['56', '65'])).
% 0.34/0.53  thf('67', plain,
% 0.34/0.53      ((((sk_A) != (sk_A)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['3', '66'])).
% 0.34/0.53  thf('68', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.34/0.53      inference('simplify', [status(thm)], ['67'])).
% 0.34/0.53  thf('69', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.34/0.53      inference('demod', [status(thm)], ['59', '64'])).
% 0.34/0.53  thf('70', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['68', '69'])).
% 0.34/0.53  thf('71', plain, ($false), inference('simplify', [status(thm)], ['70'])).
% 0.34/0.53  
% 0.34/0.53  % SZS output end Refutation
% 0.34/0.53  
% 0.34/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
