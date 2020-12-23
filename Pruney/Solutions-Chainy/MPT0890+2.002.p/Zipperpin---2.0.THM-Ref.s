%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oYUnPRSU5Q

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 205 expanded)
%              Number of leaves         :   18 (  70 expanded)
%              Depth                    :   14
%              Number of atoms          :  582 (4293 expanded)
%              Number of equality atoms :   70 ( 591 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t50_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( ( ( k5_mcart_1 @ A @ B @ C @ D )
                  = ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k6_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k7_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 )
          & ~ ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
               => ( ( ( k5_mcart_1 @ A @ B @ C @ D )
                    = ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                  & ( ( k6_mcart_1 @ A @ B @ C @ D )
                    = ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                  & ( ( k7_mcart_1 @ A @ B @ C @ D )
                    = ( k2_mcart_1 @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_mcart_1])).

thf('0',plain,
    ( ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != ( k2_mcart_1 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
   <= ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( D
                = ( k3_mcart_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ ( k6_mcart_1 @ A @ B @ C @ D ) @ ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( X9
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X6 @ X7 @ X8 @ X9 ) @ ( k6_mcart_1 @ X6 @ X7 @ X8 @ X9 ) @ ( k7_mcart_1 @ X6 @ X7 @ X8 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k3_zfmisc_1 @ X6 @ X7 @ X8 ) )
      | ( X8 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('4',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['4','5','6','7'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('10',plain,(
    ! [X10: $i,X12: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X10 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k2_mcart_1 @ sk_D )
    = ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,
    ( ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != ( k2_mcart_1 @ sk_D ) )
   <= ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != ( k2_mcart_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( ( k2_mcart_1 @ sk_D )
     != ( k2_mcart_1 @ sk_D ) )
   <= ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != ( k2_mcart_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k2_mcart_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['4','5','6','7'])).

thf('17',plain,
    ( ( k2_mcart_1 @ sk_D )
    = ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('18',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k1_mcart_1 @ sk_D )
    = ( k4_tarski @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('24',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) )
    = ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
   <= ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,
    ( ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
   <= ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
    | ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != ( k2_mcart_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,(
    ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference('sat_resolution*',[status(thm)],['15','27','28'])).

thf('30',plain,(
    ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['1','29'])).

thf('31',plain,
    ( ( k1_mcart_1 @ sk_D )
    = ( k4_tarski @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('32',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) )
    = ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('33',plain,
    ( ( k1_mcart_1 @ sk_D )
    = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X10: $i,X12: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X10 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('35',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) )
    = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) )
 != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['30','35'])).

thf('37',plain,(
    $false ),
    inference(simplify,[status(thm)],['36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oYUnPRSU5Q
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:08:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 31 iterations in 0.018s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.47  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.47  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.47  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(t50_mcart_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.47          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.47          ( ~( ![D:$i]:
% 0.20/0.47               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.47                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.47                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.20/0.47                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.47                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.20/0.47                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.47        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.47             ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.47             ( ~( ![D:$i]:
% 0.20/0.47                  ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.47                    ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.47                        ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.20/0.47                      ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.47                        ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.20/0.47                      ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t50_mcart_1])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      ((((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.47          != (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))
% 0.20/0.47        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.47            != (k2_mcart_1 @ (k1_mcart_1 @ sk_D)))
% 0.20/0.47        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k2_mcart_1 @ sk_D)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      ((((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.47          != (k2_mcart_1 @ (k1_mcart_1 @ sk_D))))
% 0.20/0.47         <= (~
% 0.20/0.47             (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.47                = (k2_mcart_1 @ (k1_mcart_1 @ sk_D)))))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('2', plain, ((m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t48_mcart_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.47          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.47          ( ~( ![D:$i]:
% 0.20/0.47               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.47                 ( ( D ) =
% 0.20/0.47                   ( k3_mcart_1 @
% 0.20/0.47                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.20/0.47                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.20/0.47                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.47         (((X6) = (k1_xboole_0))
% 0.20/0.47          | ((X7) = (k1_xboole_0))
% 0.20/0.47          | ((X9)
% 0.20/0.47              = (k3_mcart_1 @ (k5_mcart_1 @ X6 @ X7 @ X8 @ X9) @ 
% 0.20/0.47                 (k6_mcart_1 @ X6 @ X7 @ X8 @ X9) @ 
% 0.20/0.47                 (k7_mcart_1 @ X6 @ X7 @ X8 @ X9)))
% 0.20/0.47          | ~ (m1_subset_1 @ X9 @ (k3_zfmisc_1 @ X6 @ X7 @ X8))
% 0.20/0.47          | ((X8) = (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      ((((sk_C) = (k1_xboole_0))
% 0.20/0.47        | ((sk_D)
% 0.20/0.47            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.47               (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.47               (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 0.20/0.47        | ((sk_B) = (k1_xboole_0))
% 0.20/0.47        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf('5', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('6', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('7', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (((sk_D)
% 0.20/0.47         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.47            (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.47            (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['4', '5', '6', '7'])).
% 0.20/0.47  thf(d3_mcart_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.20/0.47           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.47  thf(t7_mcart_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.47       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X10 : $i, X12 : $i]: ((k2_mcart_1 @ (k4_tarski @ X10 @ X12)) = (X12))),
% 0.20/0.47      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((k2_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (X0))),
% 0.20/0.47      inference('sup+', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (((k2_mcart_1 @ sk_D) = (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.47      inference('sup+', [status(thm)], ['8', '11'])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      ((((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k2_mcart_1 @ sk_D)))
% 0.20/0.47         <= (~
% 0.20/0.47             (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k2_mcart_1 @ sk_D))))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      ((((k2_mcart_1 @ sk_D) != (k2_mcart_1 @ sk_D)))
% 0.20/0.47         <= (~
% 0.20/0.47             (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k2_mcart_1 @ sk_D))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      ((((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k2_mcart_1 @ sk_D)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (((sk_D)
% 0.20/0.47         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.47            (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.47            (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['4', '5', '6', '7'])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (((k2_mcart_1 @ sk_D) = (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.47      inference('sup+', [status(thm)], ['8', '11'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (((sk_D)
% 0.20/0.47         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.47            (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ (k2_mcart_1 @ sk_D)))),
% 0.20/0.47      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.20/0.47           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X10 : $i, X11 : $i]: ((k1_mcart_1 @ (k4_tarski @ X10 @ X11)) = (X10))),
% 0.20/0.47      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 0.20/0.47      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (((k1_mcart_1 @ sk_D)
% 0.20/0.47         = (k4_tarski @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.47            (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['18', '21'])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      (![X10 : $i, X11 : $i]: ((k1_mcart_1 @ (k4_tarski @ X10 @ X11)) = (X10))),
% 0.20/0.47      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      (((k1_mcart_1 @ (k1_mcart_1 @ sk_D))
% 0.20/0.47         = (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.47      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      ((((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.47          != (k1_mcart_1 @ (k1_mcart_1 @ sk_D))))
% 0.20/0.47         <= (~
% 0.20/0.47             (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.47                = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      ((((k1_mcart_1 @ (k1_mcart_1 @ sk_D))
% 0.20/0.47          != (k1_mcart_1 @ (k1_mcart_1 @ sk_D))))
% 0.20/0.47         <= (~
% 0.20/0.47             (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.47                = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      ((((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.47          = (k1_mcart_1 @ (k1_mcart_1 @ sk_D))))),
% 0.20/0.47      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      (~
% 0.20/0.47       (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.47          = (k2_mcart_1 @ (k1_mcart_1 @ sk_D)))) | 
% 0.20/0.47       ~
% 0.20/0.47       (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.47          = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))) | 
% 0.20/0.47       ~ (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k2_mcart_1 @ sk_D)))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      (~
% 0.20/0.47       (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.47          = (k2_mcart_1 @ (k1_mcart_1 @ sk_D))))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['15', '27', '28'])).
% 0.20/0.47  thf('30', plain,
% 0.20/0.47      (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.47         != (k2_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['1', '29'])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      (((k1_mcart_1 @ sk_D)
% 0.20/0.47         = (k4_tarski @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.47            (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['18', '21'])).
% 0.20/0.47  thf('32', plain,
% 0.20/0.47      (((k1_mcart_1 @ (k1_mcart_1 @ sk_D))
% 0.20/0.47         = (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.47      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.47  thf('33', plain,
% 0.20/0.47      (((k1_mcart_1 @ sk_D)
% 0.20/0.47         = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.20/0.47            (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.20/0.47      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.47  thf('34', plain,
% 0.20/0.47      (![X10 : $i, X12 : $i]: ((k2_mcart_1 @ (k4_tarski @ X10 @ X12)) = (X12))),
% 0.20/0.47      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      (((k2_mcart_1 @ (k1_mcart_1 @ sk_D))
% 0.20/0.47         = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.47      inference('sup+', [status(thm)], ['33', '34'])).
% 0.20/0.47  thf('36', plain,
% 0.20/0.47      (((k2_mcart_1 @ (k1_mcart_1 @ sk_D))
% 0.20/0.47         != (k2_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.20/0.47      inference('demod', [status(thm)], ['30', '35'])).
% 0.20/0.47  thf('37', plain, ($false), inference('simplify', [status(thm)], ['36'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
