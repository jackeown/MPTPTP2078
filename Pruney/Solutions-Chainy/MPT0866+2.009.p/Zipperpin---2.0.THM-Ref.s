%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1oHHUEHMvk

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 121 expanded)
%              Number of leaves         :   19 (  45 expanded)
%              Depth                    :   17
%              Number of atoms          :  365 (1174 expanded)
%              Number of equality atoms :   61 ( 182 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t24_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
             => ( C
                = ( k4_tarski @ ( k1_mcart_1 @ C ) @ ( k2_mcart_1 @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ~ ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
               => ( C
                  = ( k4_tarski @ ( k1_mcart_1 @ C ) @ ( k2_mcart_1 @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ D @ E )
           != A ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k4_tarski @ ( sk_D @ X3 ) @ ( sk_E @ X3 ) )
        = X3 )
      | ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k4_tarski @ ( sk_D @ sk_C ) @ ( sk_E @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k4_tarski @ ( sk_D @ sk_C ) @ ( sk_E @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('7',plain,
    ( ( ( k1_mcart_1 @ sk_C )
      = ( sk_D @ sk_C ) )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('9',plain,
    ( ( ( k1_mcart_1 @ sk_C )
      = ( sk_D @ sk_C ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X7 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('11',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_mcart_1 @ sk_C )
      = ( sk_D @ sk_C ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k1_mcart_1 @ sk_C )
      = ( sk_D @ sk_C ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k1_mcart_1 @ sk_C )
    = ( sk_D @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['12','13','14'])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( sk_E @ sk_C ) )
      = sk_C ) ),
    inference(demod,[status(thm)],['4','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( sk_E @ sk_C ) )
      = sk_C ) ),
    inference(demod,[status(thm)],['4','15'])).

thf('18',plain,(
    ! [X12: $i,X14: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X12 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('19',plain,
    ( ( ( k2_mcart_1 @ sk_C )
      = ( sk_E @ sk_C ) )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X7 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X1 )
       != X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( ( k2_mcart_1 @ sk_C )
      = ( sk_E @ sk_C ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k2_mcart_1 @ sk_C )
    = ( sk_E @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) )
      = sk_C ) ),
    inference(demod,[status(thm)],['16','27'])).

thf('29',plain,(
    sk_C
 != ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('32',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['32','33','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1oHHUEHMvk
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:10:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 63 iterations in 0.061s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i > $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(sk_E_type, type, sk_E: $i > $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.51  thf(t24_mcart_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.51          ( ~( ![C:$i]:
% 0.21/0.51               ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.21/0.51                 ( ( C ) =
% 0.21/0.51                   ( k4_tarski @ ( k1_mcart_1 @ C ) @ ( k2_mcart_1 @ C ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i]:
% 0.21/0.51        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.51             ( ~( ![C:$i]:
% 0.21/0.51                  ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.21/0.51                    ( ( C ) =
% 0.21/0.51                      ( k4_tarski @ ( k1_mcart_1 @ C ) @ ( k2_mcart_1 @ C ) ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t24_mcart_1])).
% 0.21/0.51  thf('0', plain, ((m1_subset_1 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d2_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.51       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X9 @ X10)
% 0.21/0.51          | (r2_hidden @ X9 @ X10)
% 0.21/0.52          | (v1_xboole_0 @ X10))),
% 0.21/0.52      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.21/0.52        | (r2_hidden @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.52  thf(l139_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.21/0.52          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.52         (((k4_tarski @ (sk_D @ X3) @ (sk_E @ X3)) = (X3))
% 0.21/0.52          | ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X4 @ X5)))),
% 0.21/0.52      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.21/0.52        | ((k4_tarski @ (sk_D @ sk_C) @ (sk_E @ sk_C)) = (sk_C)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.21/0.52        | ((k4_tarski @ (sk_D @ sk_C) @ (sk_E @ sk_C)) = (sk_C)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf(t7_mcart_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.21/0.52       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i]: ((k1_mcart_1 @ (k4_tarski @ X12 @ X13)) = (X12))),
% 0.21/0.52      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      ((((k1_mcart_1 @ sk_C) = (sk_D @ sk_C))
% 0.21/0.52        | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf(l13_xboole_0, axiom,
% 0.21/0.52    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      ((((k1_mcart_1 @ sk_C) = (sk_D @ sk_C))
% 0.21/0.52        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.52  thf(t113_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X6 : $i, X7 : $i]:
% 0.21/0.52         (((X6) = (k1_xboole_0))
% 0.21/0.52          | ((X7) = (k1_xboole_0))
% 0.21/0.52          | ((k2_zfmisc_1 @ X7 @ X6) != (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.52        | ((k1_mcart_1 @ sk_C) = (sk_D @ sk_C))
% 0.21/0.52        | ((sk_A) = (k1_xboole_0))
% 0.21/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      ((((sk_B) = (k1_xboole_0))
% 0.21/0.52        | ((sk_A) = (k1_xboole_0))
% 0.21/0.52        | ((k1_mcart_1 @ sk_C) = (sk_D @ sk_C)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.52  thf('13', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('14', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('15', plain, (((k1_mcart_1 @ sk_C) = (sk_D @ sk_C))),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['12', '13', '14'])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.21/0.52        | ((k4_tarski @ (k1_mcart_1 @ sk_C) @ (sk_E @ sk_C)) = (sk_C)))),
% 0.21/0.52      inference('demod', [status(thm)], ['4', '15'])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.21/0.52        | ((k4_tarski @ (k1_mcart_1 @ sk_C) @ (sk_E @ sk_C)) = (sk_C)))),
% 0.21/0.52      inference('demod', [status(thm)], ['4', '15'])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X12 : $i, X14 : $i]: ((k2_mcart_1 @ (k4_tarski @ X12 @ X14)) = (X14))),
% 0.21/0.52      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      ((((k2_mcart_1 @ sk_C) = (sk_E @ sk_C))
% 0.21/0.52        | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['17', '18'])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X6 : $i, X7 : $i]:
% 0.21/0.52         (((X6) = (k1_xboole_0))
% 0.21/0.52          | ((X7) = (k1_xboole_0))
% 0.21/0.52          | ((k2_zfmisc_1 @ X7 @ X6) != (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (((k2_zfmisc_1 @ X2 @ X1) != (X0))
% 0.21/0.52          | ~ (v1_xboole_0 @ X0)
% 0.21/0.52          | ((X2) = (k1_xboole_0))
% 0.21/0.52          | ((X1) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X1 : $i, X2 : $i]:
% 0.21/0.52         (((X1) = (k1_xboole_0))
% 0.21/0.52          | ((X2) = (k1_xboole_0))
% 0.21/0.52          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      ((((k2_mcart_1 @ sk_C) = (sk_E @ sk_C))
% 0.21/0.52        | ((sk_A) = (k1_xboole_0))
% 0.21/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['19', '23'])).
% 0.21/0.52  thf('25', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('26', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('27', plain, (((k2_mcart_1 @ sk_C) = (sk_E @ sk_C))),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['24', '25', '26'])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.21/0.52        | ((k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C)) = (sk_C)))),
% 0.21/0.52      inference('demod', [status(thm)], ['16', '27'])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (((sk_C) != (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('30', plain, ((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (![X1 : $i, X2 : $i]:
% 0.21/0.52         (((X1) = (k1_xboole_0))
% 0.21/0.52          | ((X2) = (k1_xboole_0))
% 0.21/0.52          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.52  thf('32', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.52  thf('33', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('34', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('35', plain, ($false),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['32', '33', '34'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
