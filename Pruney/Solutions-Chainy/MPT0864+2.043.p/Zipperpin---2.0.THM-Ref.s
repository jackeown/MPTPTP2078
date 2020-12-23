%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1IeIUW6Lhd

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 143 expanded)
%              Number of leaves         :   30 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :  610 (1177 expanded)
%              Number of equality atoms :   83 ( 179 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X7 @ X7 @ X8 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X9 @ X9 @ X10 @ X11 )
      = ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(d2_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( ( F != D )
              & ( F != C )
              & ( F != B )
              & ( F != A ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ D @ C @ B @ A )
    <=> ( ( F != A )
        & ( F != B )
        & ( F != C )
        & ( F != D ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 @ X33 )
      | ( r2_hidden @ X29 @ X34 )
      | ( X34
       != ( k2_enumset1 @ X33 @ X32 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( r2_hidden @ X29 @ ( k2_enumset1 @ X33 @ X32 @ X31 @ X30 ) )
      | ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 @ X33 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X24 != X23 )
      | ~ ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,(
    ! [X23: $i,X25: $i,X26: $i,X27: $i] :
      ~ ( zip_tseitin_0 @ X23 @ X25 @ X26 @ X27 @ X23 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('11',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X12 ) @ X14 )
      | ~ ( r2_hidden @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t20_mcart_1,conjecture,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i] :
        ( ? [B: $i,C: $i] :
            ( A
            = ( k4_tarski @ B @ C ) )
       => ( ( A
           != ( k1_mcart_1 @ A ) )
          & ( A
           != ( k2_mcart_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_mcart_1])).

thf('13',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('14',plain,(
    ! [X39: $i,X41: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X39 @ X41 ) )
      = X41 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('15',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('17',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','17'])).

thf('19',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('20',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X17 ) @ ( k2_tarski @ X18 @ X19 ) )
      = ( k2_tarski @ ( k4_tarski @ X17 @ X18 ) @ ( k4_tarski @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t135_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) )
        | ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('26',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('29',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X21 ) @ X22 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['27','30'])).

thf('32',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','31'])).

thf('33',plain,
    ( $false
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('35',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('36',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X39 @ X40 ) )
      = X39 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('37',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['16'])).

thf('39',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('43',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X17 ) @ ( k2_tarski @ X18 @ X19 ) )
      = ( k2_tarski @ ( k4_tarski @ X17 @ X18 ) @ ( k4_tarski @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ X0 ) )
        = ( k2_tarski @ sk_A @ ( k4_tarski @ sk_A @ X0 ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ ( k4_tarski @ sk_A @ X0 ) ) )
        | ( ( k1_tarski @ sk_A )
          = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('48',plain,
    ( ! [X0: $i] :
        ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ ( k4_tarski @ sk_A @ X0 ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','48'])).

thf('50',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('51',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    sk_A
 != ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','51'])).

thf('53',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['16'])).

thf('54',plain,
    ( sk_A
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['52','53'])).

thf('55',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['33','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1IeIUW6Lhd
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:25:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.58  % Solved by: fo/fo7.sh
% 0.20/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.58  % done 305 iterations in 0.131s
% 0.20/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.58  % SZS output start Refutation
% 0.20/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.58  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.58  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.20/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.58  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.58  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.58  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.58  thf(t70_enumset1, axiom,
% 0.20/0.58    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.58  thf('0', plain,
% 0.20/0.58      (![X7 : $i, X8 : $i]:
% 0.20/0.58         ((k1_enumset1 @ X7 @ X7 @ X8) = (k2_tarski @ X7 @ X8))),
% 0.20/0.58      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.58  thf(t69_enumset1, axiom,
% 0.20/0.58    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.58  thf('1', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.20/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.58  thf('2', plain,
% 0.20/0.58      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.20/0.58      inference('sup+', [status(thm)], ['0', '1'])).
% 0.20/0.58  thf(t71_enumset1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.20/0.58  thf('3', plain,
% 0.20/0.58      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.58         ((k2_enumset1 @ X9 @ X9 @ X10 @ X11) = (k1_enumset1 @ X9 @ X10 @ X11))),
% 0.20/0.58      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.20/0.58  thf(d2_enumset1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.58     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.20/0.58       ( ![F:$i]:
% 0.20/0.58         ( ( r2_hidden @ F @ E ) <=>
% 0.20/0.58           ( ~( ( ( F ) != ( D ) ) & ( ( F ) != ( C ) ) & ( ( F ) != ( B ) ) & 
% 0.20/0.58                ( ( F ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.20/0.58  thf(zf_stmt_1, axiom,
% 0.20/0.58    (![F:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.58     ( ( zip_tseitin_0 @ F @ D @ C @ B @ A ) <=>
% 0.20/0.58       ( ( ( F ) != ( A ) ) & ( ( F ) != ( B ) ) & ( ( F ) != ( C ) ) & 
% 0.20/0.58         ( ( F ) != ( D ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_2, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.58     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.20/0.58       ( ![F:$i]:
% 0.20/0.58         ( ( r2_hidden @ F @ E ) <=> ( ~( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) ) ))).
% 0.20/0.58  thf('4', plain,
% 0.20/0.58      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.58         ((zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 @ X33)
% 0.20/0.58          | (r2_hidden @ X29 @ X34)
% 0.20/0.58          | ((X34) != (k2_enumset1 @ X33 @ X32 @ X31 @ X30)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.58  thf('5', plain,
% 0.20/0.58      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.58         ((r2_hidden @ X29 @ (k2_enumset1 @ X33 @ X32 @ X31 @ X30))
% 0.20/0.58          | (zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 @ X33))),
% 0.20/0.58      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.58  thf('6', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.58         ((r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.20/0.58          | (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2))),
% 0.20/0.58      inference('sup+', [status(thm)], ['3', '5'])).
% 0.20/0.58  thf('7', plain,
% 0.20/0.58      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.58         (((X24) != (X23)) | ~ (zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 @ X23))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.58  thf('8', plain,
% 0.20/0.58      (![X23 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.58         ~ (zip_tseitin_0 @ X23 @ X25 @ X26 @ X27 @ X23)),
% 0.20/0.58      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.58  thf('9', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         (r2_hidden @ X0 @ (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.20/0.58      inference('sup-', [status(thm)], ['6', '8'])).
% 0.20/0.58  thf('10', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.58      inference('sup+', [status(thm)], ['2', '9'])).
% 0.20/0.58  thf(l1_zfmisc_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.58  thf('11', plain,
% 0.20/0.58      (![X12 : $i, X14 : $i]:
% 0.20/0.58         ((r1_tarski @ (k1_tarski @ X12) @ X14) | ~ (r2_hidden @ X12 @ X14))),
% 0.20/0.58      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.58  thf('12', plain,
% 0.20/0.58      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.58  thf(t20_mcart_1, conjecture,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.20/0.58       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_3, negated_conjecture,
% 0.20/0.58    (~( ![A:$i]:
% 0.20/0.58        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.20/0.58          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.20/0.58    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.20/0.58  thf('13', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.58  thf(t7_mcart_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.58       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.58  thf('14', plain,
% 0.20/0.58      (![X39 : $i, X41 : $i]: ((k2_mcart_1 @ (k4_tarski @ X39 @ X41)) = (X41))),
% 0.20/0.58      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.58  thf('15', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.20/0.58      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.58  thf('16', plain,
% 0.20/0.58      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.58  thf('17', plain,
% 0.20/0.58      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.58      inference('split', [status(esa)], ['16'])).
% 0.20/0.58  thf('18', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.58      inference('sup+', [status(thm)], ['15', '17'])).
% 0.20/0.58  thf('19', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.58  thf('20', plain,
% 0.20/0.58      ((((sk_A) = (k4_tarski @ sk_B @ sk_A)))
% 0.20/0.58         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.58      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.58  thf('21', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.20/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.58  thf(t36_zfmisc_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 0.20/0.58         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 0.20/0.58       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 0.20/0.58         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 0.20/0.58  thf('22', plain,
% 0.20/0.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.58         ((k2_zfmisc_1 @ (k1_tarski @ X17) @ (k2_tarski @ X18 @ X19))
% 0.20/0.58           = (k2_tarski @ (k4_tarski @ X17 @ X18) @ (k4_tarski @ X17 @ X19)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.20/0.58  thf('23', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 0.20/0.58           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.20/0.58      inference('sup+', [status(thm)], ['21', '22'])).
% 0.20/0.58  thf('24', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.20/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.58  thf('25', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.20/0.58           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.20/0.58      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.58  thf(t135_zfmisc_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) ) | 
% 0.20/0.58         ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.58       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.58  thf('26', plain,
% 0.20/0.58      (![X15 : $i, X16 : $i]:
% 0.20/0.58         (((X15) = (k1_xboole_0))
% 0.20/0.58          | ~ (r1_tarski @ X15 @ (k2_zfmisc_1 @ X16 @ X15)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.20/0.58  thf('27', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.20/0.58          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.58  thf(idempotence_k2_xboole_0, axiom,
% 0.20/0.58    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.58  thf('28', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.58      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.20/0.58  thf(t49_zfmisc_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.20/0.58  thf('29', plain,
% 0.20/0.58      (![X21 : $i, X22 : $i]:
% 0.20/0.58         ((k2_xboole_0 @ (k1_tarski @ X21) @ X22) != (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.20/0.58  thf('30', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.58  thf('31', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.20/0.58      inference('simplify_reflect-', [status(thm)], ['27', '30'])).
% 0.20/0.58  thf('32', plain,
% 0.20/0.58      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.20/0.58         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['20', '31'])).
% 0.20/0.58  thf('33', plain, (($false) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['12', '32'])).
% 0.20/0.58  thf('34', plain,
% 0.20/0.58      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.58  thf('35', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.58  thf('36', plain,
% 0.20/0.58      (![X39 : $i, X40 : $i]: ((k1_mcart_1 @ (k4_tarski @ X39 @ X40)) = (X39))),
% 0.20/0.58      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.58  thf('37', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.20/0.58      inference('sup+', [status(thm)], ['35', '36'])).
% 0.20/0.58  thf('38', plain,
% 0.20/0.58      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.58      inference('split', [status(esa)], ['16'])).
% 0.20/0.58  thf('39', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.58      inference('sup+', [status(thm)], ['37', '38'])).
% 0.20/0.58  thf('40', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.58  thf('41', plain,
% 0.20/0.58      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.20/0.58         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.58      inference('sup+', [status(thm)], ['39', '40'])).
% 0.20/0.58  thf('42', plain,
% 0.20/0.58      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.20/0.58         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.58      inference('sup+', [status(thm)], ['39', '40'])).
% 0.20/0.58  thf('43', plain,
% 0.20/0.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.58         ((k2_zfmisc_1 @ (k1_tarski @ X17) @ (k2_tarski @ X18 @ X19))
% 0.20/0.58           = (k2_tarski @ (k4_tarski @ X17 @ X18) @ (k4_tarski @ X17 @ X19)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.20/0.58  thf('44', plain,
% 0.20/0.58      ((![X0 : $i]:
% 0.20/0.58          ((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ X0))
% 0.20/0.58            = (k2_tarski @ sk_A @ (k4_tarski @ sk_A @ X0))))
% 0.20/0.58         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.58      inference('sup+', [status(thm)], ['42', '43'])).
% 0.20/0.58  thf('45', plain,
% 0.20/0.58      (![X15 : $i, X16 : $i]:
% 0.20/0.58         (((X15) = (k1_xboole_0))
% 0.20/0.58          | ~ (r1_tarski @ X15 @ (k2_zfmisc_1 @ X15 @ X16)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.20/0.58  thf('46', plain,
% 0.20/0.58      ((![X0 : $i]:
% 0.20/0.58          (~ (r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.20/0.58              (k2_tarski @ sk_A @ (k4_tarski @ sk_A @ X0)))
% 0.20/0.58           | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.20/0.58         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.58  thf('47', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.58  thf('48', plain,
% 0.20/0.58      ((![X0 : $i]:
% 0.20/0.58          ~ (r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.20/0.58             (k2_tarski @ sk_A @ (k4_tarski @ sk_A @ X0))))
% 0.20/0.58         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.58      inference('simplify_reflect-', [status(thm)], ['46', '47'])).
% 0.20/0.58  thf('49', plain,
% 0.20/0.58      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_A)))
% 0.20/0.58         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['41', '48'])).
% 0.20/0.58  thf('50', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.20/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.58  thf('51', plain,
% 0.20/0.58      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.20/0.58         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.58      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.58  thf('52', plain, (~ (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['34', '51'])).
% 0.20/0.58  thf('53', plain,
% 0.20/0.58      ((((sk_A) = (k2_mcart_1 @ sk_A))) | (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.20/0.58      inference('split', [status(esa)], ['16'])).
% 0.20/0.58  thf('54', plain, ((((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.20/0.58      inference('sat_resolution*', [status(thm)], ['52', '53'])).
% 0.20/0.58  thf('55', plain, ($false),
% 0.20/0.58      inference('simpl_trail', [status(thm)], ['33', '54'])).
% 0.20/0.58  
% 0.20/0.58  % SZS output end Refutation
% 0.20/0.58  
% 0.42/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
