%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SAKfXESYEL

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  68 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :  564 (1544 expanded)
%              Number of equality atoms :   44 ( 184 expanded)
%              Maximal formula depth    :   24 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(t82_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( ! [G: $i] :
            ( ( m1_subset_1 @ G @ A )
           => ! [H: $i] :
                ( ( m1_subset_1 @ H @ B )
               => ! [I: $i] :
                    ( ( m1_subset_1 @ I @ C )
                   => ! [J: $i] :
                        ( ( m1_subset_1 @ J @ D )
                       => ( ( F
                            = ( k4_mcart_1 @ G @ H @ I @ J ) )
                         => ( E = J ) ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D = k1_xboole_0 )
          | ( E
            = ( k11_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
       => ( ! [G: $i] :
              ( ( m1_subset_1 @ G @ A )
             => ! [H: $i] :
                  ( ( m1_subset_1 @ H @ B )
                 => ! [I: $i] :
                      ( ( m1_subset_1 @ I @ C )
                     => ! [J: $i] :
                          ( ( m1_subset_1 @ J @ D )
                         => ( ( F
                              = ( k4_mcart_1 @ G @ H @ I @ J ) )
                           => ( E = J ) ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D = k1_xboole_0 )
            | ( E
              = ( k11_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t82_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t60_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 )
        & ~ ! [E: $i] :
              ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
             => ( E
                = ( k4_mcart_1 @ ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ ( k11_mcart_1 @ A @ B @ C @ D @ E ) ) ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X24
        = ( k4_mcart_1 @ ( k8_mcart_1 @ X20 @ X21 @ X22 @ X23 @ X24 ) @ ( k9_mcart_1 @ X20 @ X21 @ X22 @ X23 @ X24 ) @ ( k10_mcart_1 @ X20 @ X21 @ X22 @ X23 @ X24 ) @ ( k11_mcart_1 @ X20 @ X21 @ X22 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k4_zfmisc_1 @ X20 @ X21 @ X22 @ X23 ) )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t60_mcart_1])).

thf('2',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_F
      = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ) )
    | ( sk_C = k1_xboole_0 )
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

thf('6',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( sk_F
    = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ B ) ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k9_mcart_1 @ X15 @ X16 @ X17 @ X18 @ X19 ) @ X16 )
      | ~ ( m1_subset_1 @ X19 @ ( k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_mcart_1])).

thf('10',plain,(
    m1_subset_1 @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ sk_B )
      | ~ ( m1_subset_1 @ X26 @ sk_D )
      | ( sk_E = X26 )
      | ( sk_F
       != ( k4_mcart_1 @ X27 @ X25 @ X28 @ X26 ) )
      | ~ ( m1_subset_1 @ X28 @ sk_C )
      | ~ ( m1_subset_1 @ X27 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_F
       != ( k4_mcart_1 @ X0 @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ X1 @ X2 ) )
      | ( sk_E = X2 )
      | ~ ( m1_subset_1 @ X2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_F != sk_F )
    | ~ ( m1_subset_1 @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ sk_D )
    | ( sk_E
      = ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
    | ~ ( m1_subset_1 @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k11_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k11_mcart_1 @ A @ B @ C @ D @ E ) @ D ) ) )).

thf('15',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k11_mcart_1 @ X5 @ X6 @ X7 @ X8 @ X9 ) @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k11_mcart_1])).

thf('16',plain,(
    m1_subset_1 @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ sk_D ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ C ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k10_mcart_1 @ X0 @ X1 @ X2 @ X3 @ X4 ) @ X2 )
      | ~ ( m1_subset_1 @ X4 @ ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_mcart_1])).

thf('19',plain,(
    m1_subset_1 @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ A ) ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k8_mcart_1 @ X10 @ X11 @ X12 @ X13 @ X14 ) @ X10 )
      | ~ ( m1_subset_1 @ X14 @ ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_mcart_1])).

thf('22',plain,(
    m1_subset_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_F != sk_F )
    | ( sk_E
      = ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['13','16','19','22'])).

thf('24',plain,
    ( sk_E
    = ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    sk_E
 != ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SAKfXESYEL
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:07:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 17 iterations in 0.015s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.47  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.47  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.47  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.47  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.47  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.47  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.21/0.47  thf(t82_mcart_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.21/0.47       ( ( ![G:$i]:
% 0.21/0.47           ( ( m1_subset_1 @ G @ A ) =>
% 0.21/0.47             ( ![H:$i]:
% 0.21/0.47               ( ( m1_subset_1 @ H @ B ) =>
% 0.21/0.47                 ( ![I:$i]:
% 0.21/0.47                   ( ( m1_subset_1 @ I @ C ) =>
% 0.21/0.47                     ( ![J:$i]:
% 0.21/0.47                       ( ( m1_subset_1 @ J @ D ) =>
% 0.21/0.47                         ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.21/0.47                           ( ( E ) = ( J ) ) ) ) ) ) ) ) ) ) ) =>
% 0.21/0.47         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.47           ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.21/0.47           ( ( E ) = ( k11_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.47        ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.21/0.47          ( ( ![G:$i]:
% 0.21/0.47              ( ( m1_subset_1 @ G @ A ) =>
% 0.21/0.47                ( ![H:$i]:
% 0.21/0.47                  ( ( m1_subset_1 @ H @ B ) =>
% 0.21/0.47                    ( ![I:$i]:
% 0.21/0.47                      ( ( m1_subset_1 @ I @ C ) =>
% 0.21/0.47                        ( ![J:$i]:
% 0.21/0.47                          ( ( m1_subset_1 @ J @ D ) =>
% 0.21/0.47                            ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.21/0.47                              ( ( E ) = ( J ) ) ) ) ) ) ) ) ) ) ) =>
% 0.21/0.47            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.47              ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.21/0.47              ( ( E ) = ( k11_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t82_mcart_1])).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t60_mcart_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.47          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.21/0.47          ( ~( ![E:$i]:
% 0.21/0.47               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.21/0.47                 ( ( E ) =
% 0.21/0.47                   ( k4_mcart_1 @
% 0.21/0.47                     ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ 
% 0.21/0.47                     ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ 
% 0.21/0.47                     ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ 
% 0.21/0.47                     ( k11_mcart_1 @ A @ B @ C @ D @ E ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.47         (((X20) = (k1_xboole_0))
% 0.21/0.47          | ((X21) = (k1_xboole_0))
% 0.21/0.47          | ((X22) = (k1_xboole_0))
% 0.21/0.47          | ((X24)
% 0.21/0.47              = (k4_mcart_1 @ (k8_mcart_1 @ X20 @ X21 @ X22 @ X23 @ X24) @ 
% 0.21/0.47                 (k9_mcart_1 @ X20 @ X21 @ X22 @ X23 @ X24) @ 
% 0.21/0.47                 (k10_mcart_1 @ X20 @ X21 @ X22 @ X23 @ X24) @ 
% 0.21/0.47                 (k11_mcart_1 @ X20 @ X21 @ X22 @ X23 @ X24)))
% 0.21/0.47          | ~ (m1_subset_1 @ X24 @ (k4_zfmisc_1 @ X20 @ X21 @ X22 @ X23))
% 0.21/0.47          | ((X23) = (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t60_mcart_1])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      ((((sk_D) = (k1_xboole_0))
% 0.21/0.47        | ((sk_F)
% 0.21/0.47            = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.21/0.47               (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.21/0.47               (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.21/0.47               (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)))
% 0.21/0.47        | ((sk_C) = (k1_xboole_0))
% 0.21/0.47        | ((sk_B) = (k1_xboole_0))
% 0.21/0.47        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.47  thf('3', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('4', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('5', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('6', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (((sk_F)
% 0.21/0.47         = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.21/0.47            (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.21/0.47            (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.21/0.47            (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)))),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(dt_k9_mcart_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.21/0.47       ( m1_subset_1 @ ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ B ) ))).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.47         ((m1_subset_1 @ (k9_mcart_1 @ X15 @ X16 @ X17 @ X18 @ X19) @ X16)
% 0.21/0.47          | ~ (m1_subset_1 @ X19 @ (k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18)))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k9_mcart_1])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      ((m1_subset_1 @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ sk_B)),
% 0.21/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X25 @ sk_B)
% 0.21/0.47          | ~ (m1_subset_1 @ X26 @ sk_D)
% 0.21/0.47          | ((sk_E) = (X26))
% 0.21/0.47          | ((sk_F) != (k4_mcart_1 @ X27 @ X25 @ X28 @ X26))
% 0.21/0.47          | ~ (m1_subset_1 @ X28 @ sk_C)
% 0.21/0.47          | ~ (m1_subset_1 @ X27 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.47          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.21/0.47          | ((sk_F)
% 0.21/0.47              != (k4_mcart_1 @ X0 @ 
% 0.21/0.47                  (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ X1 @ X2))
% 0.21/0.47          | ((sk_E) = (X2))
% 0.21/0.47          | ~ (m1_subset_1 @ X2 @ sk_D))),
% 0.21/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      ((((sk_F) != (sk_F))
% 0.21/0.47        | ~ (m1_subset_1 @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.21/0.47             sk_D)
% 0.21/0.47        | ((sk_E) = (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.21/0.47        | ~ (m1_subset_1 @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.21/0.47             sk_C)
% 0.21/0.47        | ~ (m1_subset_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.21/0.47             sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['7', '12'])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(dt_k11_mcart_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.21/0.47       ( m1_subset_1 @ ( k11_mcart_1 @ A @ B @ C @ D @ E ) @ D ) ))).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.47         ((m1_subset_1 @ (k11_mcart_1 @ X5 @ X6 @ X7 @ X8 @ X9) @ X8)
% 0.21/0.47          | ~ (m1_subset_1 @ X9 @ (k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8)))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k11_mcart_1])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      ((m1_subset_1 @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ sk_D)),
% 0.21/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(dt_k10_mcart_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.21/0.47       ( m1_subset_1 @ ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ C ) ))).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.47         ((m1_subset_1 @ (k10_mcart_1 @ X0 @ X1 @ X2 @ X3 @ X4) @ X2)
% 0.21/0.47          | ~ (m1_subset_1 @ X4 @ (k4_zfmisc_1 @ X0 @ X1 @ X2 @ X3)))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k10_mcart_1])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      ((m1_subset_1 @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ sk_C)),
% 0.21/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(dt_k8_mcart_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.21/0.47       ( m1_subset_1 @ ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ A ) ))).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.47         ((m1_subset_1 @ (k8_mcart_1 @ X10 @ X11 @ X12 @ X13 @ X14) @ X10)
% 0.21/0.47          | ~ (m1_subset_1 @ X14 @ (k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k8_mcart_1])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      ((m1_subset_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ sk_A)),
% 0.21/0.47      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      ((((sk_F) != (sk_F))
% 0.21/0.47        | ((sk_E) = (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)))),
% 0.21/0.47      inference('demod', [status(thm)], ['13', '16', '19', '22'])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      (((sk_E) = (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))),
% 0.21/0.47      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      (((sk_E) != (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('26', plain, ($false),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
