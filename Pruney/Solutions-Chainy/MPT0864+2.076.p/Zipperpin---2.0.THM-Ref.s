%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GCF0bgx1M3

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:10 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 235 expanded)
%              Number of leaves         :   25 (  80 expanded)
%              Depth                    :   16
%              Number of atoms          :  587 (1863 expanded)
%              Number of equality atoms :  110 ( 306 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X31: $i] :
      ( ( X31 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X31 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X20 ) @ ( k1_tarski @ X21 ) )
        = ( k1_tarski @ X20 ) )
      | ( X20 = X21 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X22 != X24 )
      | ~ ( r2_hidden @ X22 @ ( k4_xboole_0 @ X23 @ ( k1_tarski @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('3',plain,(
    ! [X23: $i,X24: $i] :
      ~ ( r2_hidden @ X24 @ ( k4_xboole_0 @ X23 @ ( k1_tarski @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( sk_B @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X31: $i] :
      ( ( X31 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X31 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20 != X19 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X20 ) @ ( k1_tarski @ X19 ) )
       != ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('10',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X19 ) @ ( k1_tarski @ X19 ) )
     != ( k1_tarski @ X19 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ X19 ) @ ( k1_tarski @ X19 ) )
     != ( k1_tarski @ X19 ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('16',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X19: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X19 ) ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['8','20'])).

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
    ! [X28: $i,X29: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X28 @ X29 ) )
      = X28 ) ),
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

thf('30',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( X31 = k1_xboole_0 )
      | ~ ( r2_hidden @ X33 @ X31 )
      | ( ( sk_B @ X31 )
       != ( k4_tarski @ X33 @ X32 ) ) ) ),
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

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('33',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('34',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( sk_B @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( sk_B @ ( k2_tarski @ X0 @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X19: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X19 ) ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('38',plain,(
    ! [X0: $i] :
      ( X0
      = ( sk_B @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( X0
      = ( sk_B @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','38'])).

thf('40',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( sk_A != sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','39'])).

thf('41',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['8','20'])).

thf('43',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X28: $i,X30: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X28 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('45',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['25'])).

thf('47',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( X31 = k1_xboole_0 )
      | ~ ( r2_hidden @ X32 @ X31 )
      | ( ( sk_B @ X31 )
       != ( k4_tarski @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_A ) )
       != sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( X0
      = ( sk_B @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','38'])).

thf('54',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( sk_A != sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X19: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X19 ) ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('57',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['25'])).

thf('60',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['41','60'])).

thf('62',plain,(
    ! [X19: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X19 ) ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('63',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference(simplify,[status(thm)],['63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GCF0bgx1M3
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:08:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 159 iterations in 0.068s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.38/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.38/0.57  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.38/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.57  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.38/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.57  thf(t9_mcart_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.38/0.57          ( ![B:$i]:
% 0.38/0.57            ( ~( ( r2_hidden @ B @ A ) & 
% 0.38/0.57                 ( ![C:$i,D:$i]:
% 0.38/0.57                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.38/0.57                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.57  thf('0', plain,
% 0.38/0.57      (![X31 : $i]:
% 0.38/0.57         (((X31) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X31) @ X31))),
% 0.38/0.57      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.38/0.57  thf(t20_zfmisc_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.38/0.57         ( k1_tarski @ A ) ) <=>
% 0.38/0.57       ( ( A ) != ( B ) ) ))).
% 0.38/0.57  thf('1', plain,
% 0.38/0.57      (![X20 : $i, X21 : $i]:
% 0.38/0.57         (((k4_xboole_0 @ (k1_tarski @ X20) @ (k1_tarski @ X21))
% 0.38/0.57            = (k1_tarski @ X20))
% 0.38/0.57          | ((X20) = (X21)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.38/0.57  thf(t64_zfmisc_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.38/0.57       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.38/0.57  thf('2', plain,
% 0.38/0.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.38/0.57         (((X22) != (X24))
% 0.38/0.57          | ~ (r2_hidden @ X22 @ (k4_xboole_0 @ X23 @ (k1_tarski @ X24))))),
% 0.38/0.57      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.38/0.57  thf('3', plain,
% 0.38/0.57      (![X23 : $i, X24 : $i]:
% 0.38/0.57         ~ (r2_hidden @ X24 @ (k4_xboole_0 @ X23 @ (k1_tarski @ X24)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['2'])).
% 0.38/0.57  thf('4', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['1', '3'])).
% 0.38/0.57  thf('5', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.38/0.57          | ((X0) = (sk_B @ (k1_tarski @ X0))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['0', '4'])).
% 0.38/0.57  thf('6', plain,
% 0.38/0.57      (![X31 : $i]:
% 0.38/0.57         (((X31) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X31) @ X31))),
% 0.38/0.57      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.38/0.57  thf('7', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.38/0.57          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.38/0.57          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['5', '6'])).
% 0.38/0.57  thf('8', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.38/0.57          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['7'])).
% 0.38/0.57  thf('9', plain,
% 0.38/0.57      (![X19 : $i, X20 : $i]:
% 0.38/0.57         (((X20) != (X19))
% 0.38/0.57          | ((k4_xboole_0 @ (k1_tarski @ X20) @ (k1_tarski @ X19))
% 0.38/0.57              != (k1_tarski @ X20)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.38/0.57  thf('10', plain,
% 0.38/0.57      (![X19 : $i]:
% 0.38/0.57         ((k4_xboole_0 @ (k1_tarski @ X19) @ (k1_tarski @ X19))
% 0.38/0.57           != (k1_tarski @ X19))),
% 0.38/0.57      inference('simplify', [status(thm)], ['9'])).
% 0.38/0.57  thf(idempotence_k3_xboole_0, axiom,
% 0.38/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.38/0.57  thf('11', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.38/0.57      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.38/0.57  thf(t100_xboole_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.38/0.57  thf('12', plain,
% 0.38/0.57      (![X1 : $i, X2 : $i]:
% 0.38/0.57         ((k4_xboole_0 @ X1 @ X2)
% 0.38/0.57           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.57  thf('13', plain,
% 0.38/0.57      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['11', '12'])).
% 0.38/0.57  thf('14', plain,
% 0.38/0.57      (![X19 : $i]:
% 0.38/0.57         ((k5_xboole_0 @ (k1_tarski @ X19) @ (k1_tarski @ X19))
% 0.38/0.57           != (k1_tarski @ X19))),
% 0.38/0.57      inference('demod', [status(thm)], ['10', '13'])).
% 0.38/0.57  thf(t21_xboole_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.38/0.57  thf('15', plain,
% 0.38/0.57      (![X3 : $i, X4 : $i]:
% 0.38/0.57         ((k3_xboole_0 @ X3 @ (k2_xboole_0 @ X3 @ X4)) = (X3))),
% 0.38/0.57      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.38/0.57  thf('16', plain,
% 0.38/0.57      (![X1 : $i, X2 : $i]:
% 0.38/0.57         ((k4_xboole_0 @ X1 @ X2)
% 0.38/0.57           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.57  thf('17', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.38/0.57           = (k5_xboole_0 @ X0 @ X0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['15', '16'])).
% 0.38/0.57  thf(t46_xboole_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.38/0.57  thf('18', plain,
% 0.38/0.57      (![X5 : $i, X6 : $i]:
% 0.38/0.57         ((k4_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6)) = (k1_xboole_0))),
% 0.38/0.57      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.38/0.57  thf('19', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['17', '18'])).
% 0.38/0.57  thf('20', plain, (![X19 : $i]: ((k1_xboole_0) != (k1_tarski @ X19))),
% 0.38/0.57      inference('demod', [status(thm)], ['14', '19'])).
% 0.38/0.57  thf('21', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.38/0.57      inference('clc', [status(thm)], ['8', '20'])).
% 0.38/0.57  thf(t20_mcart_1, conjecture,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.38/0.57       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i]:
% 0.38/0.57        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.38/0.57          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.38/0.57  thf('22', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(t7_mcart_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.38/0.57       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.38/0.57  thf('23', plain,
% 0.38/0.57      (![X28 : $i, X29 : $i]: ((k1_mcart_1 @ (k4_tarski @ X28 @ X29)) = (X28))),
% 0.38/0.57      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.38/0.57  thf('24', plain, (((k1_mcart_1 @ sk_A) = (sk_B_1))),
% 0.38/0.57      inference('sup+', [status(thm)], ['22', '23'])).
% 0.38/0.57  thf('25', plain,
% 0.38/0.57      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('26', plain,
% 0.38/0.57      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.57      inference('split', [status(esa)], ['25'])).
% 0.38/0.57  thf('27', plain,
% 0.38/0.57      ((((sk_A) = (sk_B_1))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.57      inference('sup+', [status(thm)], ['24', '26'])).
% 0.38/0.57  thf('28', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('29', plain,
% 0.38/0.57      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.38/0.57         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.57      inference('sup+', [status(thm)], ['27', '28'])).
% 0.38/0.57  thf('30', plain,
% 0.38/0.57      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.38/0.57         (((X31) = (k1_xboole_0))
% 0.38/0.57          | ~ (r2_hidden @ X33 @ X31)
% 0.38/0.57          | ((sk_B @ X31) != (k4_tarski @ X33 @ X32)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.38/0.57  thf('31', plain,
% 0.38/0.57      ((![X0 : $i]:
% 0.38/0.57          (((sk_B @ X0) != (sk_A))
% 0.38/0.57           | ~ (r2_hidden @ sk_A @ X0)
% 0.38/0.57           | ((X0) = (k1_xboole_0))))
% 0.38/0.57         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['29', '30'])).
% 0.38/0.57  thf('32', plain,
% 0.38/0.57      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.38/0.57         | ((sk_B @ (k1_tarski @ sk_A)) != (sk_A))))
% 0.38/0.57         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['21', '31'])).
% 0.38/0.57  thf(t69_enumset1, axiom,
% 0.38/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.38/0.57  thf('33', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.38/0.57  thf('34', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.38/0.57  thf('35', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.38/0.57          | ((X0) = (sk_B @ (k1_tarski @ X0))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['0', '4'])).
% 0.38/0.57  thf('36', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (((X0) = (sk_B @ (k2_tarski @ X0 @ X0)))
% 0.38/0.57          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['34', '35'])).
% 0.38/0.57  thf('37', plain, (![X19 : $i]: ((k1_xboole_0) != (k1_tarski @ X19))),
% 0.38/0.57      inference('demod', [status(thm)], ['14', '19'])).
% 0.38/0.57  thf('38', plain, (![X0 : $i]: ((X0) = (sk_B @ (k2_tarski @ X0 @ X0)))),
% 0.38/0.57      inference('clc', [status(thm)], ['36', '37'])).
% 0.38/0.57  thf('39', plain, (![X0 : $i]: ((X0) = (sk_B @ (k1_tarski @ X0)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['33', '38'])).
% 0.38/0.57  thf('40', plain,
% 0.38/0.57      (((((k1_tarski @ sk_A) = (k1_xboole_0)) | ((sk_A) != (sk_A))))
% 0.38/0.57         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['32', '39'])).
% 0.38/0.57  thf('41', plain,
% 0.38/0.57      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.38/0.57         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.57      inference('simplify', [status(thm)], ['40'])).
% 0.38/0.57  thf('42', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.38/0.57      inference('clc', [status(thm)], ['8', '20'])).
% 0.38/0.57  thf('43', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('44', plain,
% 0.38/0.57      (![X28 : $i, X30 : $i]: ((k2_mcart_1 @ (k4_tarski @ X28 @ X30)) = (X30))),
% 0.38/0.57      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.38/0.57  thf('45', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.38/0.57      inference('sup+', [status(thm)], ['43', '44'])).
% 0.38/0.57  thf('46', plain,
% 0.38/0.57      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.57      inference('split', [status(esa)], ['25'])).
% 0.38/0.57  thf('47', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.57      inference('sup+', [status(thm)], ['45', '46'])).
% 0.38/0.57  thf('48', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('49', plain,
% 0.38/0.57      ((((sk_A) = (k4_tarski @ sk_B_1 @ sk_A)))
% 0.38/0.57         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.57      inference('sup+', [status(thm)], ['47', '48'])).
% 0.38/0.57  thf('50', plain,
% 0.38/0.57      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.38/0.57         (((X31) = (k1_xboole_0))
% 0.38/0.57          | ~ (r2_hidden @ X32 @ X31)
% 0.38/0.57          | ((sk_B @ X31) != (k4_tarski @ X33 @ X32)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.38/0.57  thf('51', plain,
% 0.38/0.57      ((![X0 : $i]:
% 0.38/0.57          (((sk_B @ X0) != (sk_A))
% 0.38/0.57           | ~ (r2_hidden @ sk_A @ X0)
% 0.38/0.57           | ((X0) = (k1_xboole_0))))
% 0.38/0.57         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['49', '50'])).
% 0.38/0.57  thf('52', plain,
% 0.38/0.57      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.38/0.57         | ((sk_B @ (k1_tarski @ sk_A)) != (sk_A))))
% 0.38/0.57         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['42', '51'])).
% 0.38/0.57  thf('53', plain, (![X0 : $i]: ((X0) = (sk_B @ (k1_tarski @ X0)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['33', '38'])).
% 0.38/0.57  thf('54', plain,
% 0.38/0.57      (((((k1_tarski @ sk_A) = (k1_xboole_0)) | ((sk_A) != (sk_A))))
% 0.38/0.57         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['52', '53'])).
% 0.38/0.57  thf('55', plain,
% 0.38/0.57      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.38/0.57         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.57      inference('simplify', [status(thm)], ['54'])).
% 0.38/0.57  thf('56', plain, (![X19 : $i]: ((k1_xboole_0) != (k1_tarski @ X19))),
% 0.38/0.57      inference('demod', [status(thm)], ['14', '19'])).
% 0.38/0.57  thf('57', plain,
% 0.38/0.57      ((((k1_xboole_0) != (k1_xboole_0))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['55', '56'])).
% 0.38/0.57  thf('58', plain, (~ (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['57'])).
% 0.38/0.57  thf('59', plain,
% 0.38/0.57      ((((sk_A) = (k1_mcart_1 @ sk_A))) | (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.38/0.57      inference('split', [status(esa)], ['25'])).
% 0.38/0.57  thf('60', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.38/0.57      inference('sat_resolution*', [status(thm)], ['58', '59'])).
% 0.38/0.57  thf('61', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.38/0.57      inference('simpl_trail', [status(thm)], ['41', '60'])).
% 0.38/0.57  thf('62', plain, (![X19 : $i]: ((k1_xboole_0) != (k1_tarski @ X19))),
% 0.38/0.57      inference('demod', [status(thm)], ['14', '19'])).
% 0.38/0.57  thf('63', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['61', '62'])).
% 0.38/0.57  thf('64', plain, ($false), inference('simplify', [status(thm)], ['63'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.38/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
