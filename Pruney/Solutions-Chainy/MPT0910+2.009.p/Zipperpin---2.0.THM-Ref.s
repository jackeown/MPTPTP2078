%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CJaUfEtm8f

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   41 (  57 expanded)
%              Number of leaves         :   17 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :  408 (1048 expanded)
%              Number of equality atoms :   36 ( 132 expanded)
%              Maximal formula depth    :   20 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t70_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( ! [F: $i] :
            ( ( m1_subset_1 @ F @ A )
           => ! [G: $i] :
                ( ( m1_subset_1 @ G @ B )
               => ! [H: $i] :
                    ( ( m1_subset_1 @ H @ C )
                   => ( ( E
                        = ( k3_mcart_1 @ F @ G @ H ) )
                     => ( D = G ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D
            = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) )
       => ( ! [F: $i] :
              ( ( m1_subset_1 @ F @ A )
             => ! [G: $i] :
                  ( ( m1_subset_1 @ G @ B )
                 => ! [H: $i] :
                      ( ( m1_subset_1 @ H @ C )
                     => ( ( E
                          = ( k3_mcart_1 @ F @ G @ H ) )
                       => ( D = G ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D
              = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t70_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
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

thf('1',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ( X21
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X18 @ X19 @ X20 @ X21 ) @ ( k6_mcart_1 @ X18 @ X19 @ X20 @ X21 ) @ ( k7_mcart_1 @ X18 @ X19 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k3_zfmisc_1 @ X18 @ X19 @ X20 ) )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('2',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_E
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( sk_E
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k6_mcart_1 @ X10 @ X11 @ X12 @ X13 ) @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_mcart_1])).

thf('9',plain,(
    m1_subset_1 @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ sk_B )
      | ( sk_D = X22 )
      | ( sk_E
       != ( k3_mcart_1 @ X23 @ X22 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ sk_C )
      | ~ ( m1_subset_1 @ X23 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ X1 ) )
      | ( sk_D
        = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    sk_D
 != ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ X1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_E != sk_E )
    | ~ ( m1_subset_1 @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ) )).

thf('16',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k7_mcart_1 @ X14 @ X15 @ X16 @ X17 ) @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k3_zfmisc_1 @ X14 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_mcart_1])).

thf('17',plain,(
    m1_subset_1 @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_C ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ A ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k5_mcart_1 @ X6 @ X7 @ X8 @ X9 ) @ X6 )
      | ~ ( m1_subset_1 @ X9 @ ( k3_zfmisc_1 @ X6 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_mcart_1])).

thf('20',plain,(
    m1_subset_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    sk_E != sk_E ),
    inference(demod,[status(thm)],['14','17','20'])).

thf('22',plain,(
    $false ),
    inference(simplify,[status(thm)],['21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CJaUfEtm8f
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:00:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 20 iterations in 0.015s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.47  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.47  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.47  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(t70_mcart_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.47       ( ( ![F:$i]:
% 0.20/0.47           ( ( m1_subset_1 @ F @ A ) =>
% 0.20/0.47             ( ![G:$i]:
% 0.20/0.47               ( ( m1_subset_1 @ G @ B ) =>
% 0.20/0.47                 ( ![H:$i]:
% 0.20/0.47                   ( ( m1_subset_1 @ H @ C ) =>
% 0.20/0.47                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.20/0.47                       ( ( D ) = ( G ) ) ) ) ) ) ) ) ) =>
% 0.20/0.47         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.47           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.20/0.47           ( ( D ) = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.47        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.47          ( ( ![F:$i]:
% 0.20/0.47              ( ( m1_subset_1 @ F @ A ) =>
% 0.20/0.47                ( ![G:$i]:
% 0.20/0.47                  ( ( m1_subset_1 @ G @ B ) =>
% 0.20/0.47                    ( ![H:$i]:
% 0.20/0.47                      ( ( m1_subset_1 @ H @ C ) =>
% 0.20/0.47                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.20/0.47                          ( ( D ) = ( G ) ) ) ) ) ) ) ) ) =>
% 0.20/0.47            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.47              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.20/0.47              ( ( D ) = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t70_mcart_1])).
% 0.20/0.47  thf('0', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
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
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.47         (((X18) = (k1_xboole_0))
% 0.20/0.47          | ((X19) = (k1_xboole_0))
% 0.20/0.47          | ((X21)
% 0.20/0.47              = (k3_mcart_1 @ (k5_mcart_1 @ X18 @ X19 @ X20 @ X21) @ 
% 0.20/0.47                 (k6_mcart_1 @ X18 @ X19 @ X20 @ X21) @ 
% 0.20/0.47                 (k7_mcart_1 @ X18 @ X19 @ X20 @ X21)))
% 0.20/0.47          | ~ (m1_subset_1 @ X21 @ (k3_zfmisc_1 @ X18 @ X19 @ X20))
% 0.20/0.47          | ((X20) = (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      ((((sk_C) = (k1_xboole_0))
% 0.20/0.47        | ((sk_E)
% 0.20/0.47            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.47               (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.47               (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 0.20/0.47        | ((sk_B) = (k1_xboole_0))
% 0.20/0.47        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.47  thf('3', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('4', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('5', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (((sk_E)
% 0.20/0.47         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.47            (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.47            (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5'])).
% 0.20/0.47  thf('7', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(dt_k6_mcart_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.47       ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ))).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.47         ((m1_subset_1 @ (k6_mcart_1 @ X10 @ X11 @ X12 @ X13) @ X11)
% 0.20/0.47          | ~ (m1_subset_1 @ X13 @ (k3_zfmisc_1 @ X10 @ X11 @ X12)))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k6_mcart_1])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      ((m1_subset_1 @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_B)),
% 0.20/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X22 @ sk_B)
% 0.20/0.47          | ((sk_D) = (X22))
% 0.20/0.47          | ((sk_E) != (k3_mcart_1 @ X23 @ X22 @ X24))
% 0.20/0.47          | ~ (m1_subset_1 @ X24 @ sk_C)
% 0.20/0.47          | ~ (m1_subset_1 @ X23 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.47          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.20/0.47          | ((sk_E)
% 0.20/0.47              != (k3_mcart_1 @ X0 @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.47                  X1))
% 0.20/0.47          | ((sk_D) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('12', plain, (((sk_D) != (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.47          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.20/0.47          | ((sk_E)
% 0.20/0.47              != (k3_mcart_1 @ X0 @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.47                  X1)))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      ((((sk_E) != (sk_E))
% 0.20/0.47        | ~ (m1_subset_1 @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_C)
% 0.20/0.47        | ~ (m1_subset_1 @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['6', '13'])).
% 0.20/0.47  thf('15', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(dt_k7_mcart_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.47       ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ))).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.47         ((m1_subset_1 @ (k7_mcart_1 @ X14 @ X15 @ X16 @ X17) @ X16)
% 0.20/0.47          | ~ (m1_subset_1 @ X17 @ (k3_zfmisc_1 @ X14 @ X15 @ X16)))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k7_mcart_1])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      ((m1_subset_1 @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_C)),
% 0.20/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.47  thf('18', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(dt_k5_mcart_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.47       ( m1_subset_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ A ) ))).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.47         ((m1_subset_1 @ (k5_mcart_1 @ X6 @ X7 @ X8 @ X9) @ X6)
% 0.20/0.47          | ~ (m1_subset_1 @ X9 @ (k3_zfmisc_1 @ X6 @ X7 @ X8)))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k5_mcart_1])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      ((m1_subset_1 @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_A)),
% 0.20/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.47  thf('21', plain, (((sk_E) != (sk_E))),
% 0.20/0.47      inference('demod', [status(thm)], ['14', '17', '20'])).
% 0.20/0.47  thf('22', plain, ($false), inference('simplify', [status(thm)], ['21'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
