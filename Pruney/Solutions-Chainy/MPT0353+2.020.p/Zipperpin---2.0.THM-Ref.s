%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VAZe9Nhgzg

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:16 EST 2020

% Result     : Theorem 0.98s
% Output     : Refutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :   59 (  67 expanded)
%              Number of leaves         :   26 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  379 ( 531 expanded)
%              Number of equality atoms :   29 (  37 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t32_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( k7_subset_1 @ A @ B @ C )
              = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_subset_1])).

thf('0',plain,(
    ( k7_subset_1 @ sk_A @ sk_B @ sk_C_1 )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k4_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ sk_A @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ( k4_xboole_0 @ sk_B @ sk_C_1 )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('7',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k9_subset_1 @ X27 @ X25 @ X26 )
        = ( k3_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      = ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ X15 )
      | ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('13',plain,(
    ! [X21: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('14',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r1_tarski @ X12 @ X10 )
      | ( X11
       != ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('16',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['14','16'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('23',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X17 @ X18 )
        = ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('26',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf('30',plain,(
    ( k4_xboole_0 @ sk_B @ sk_C_1 )
 != ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['4','9','29'])).

thf('31',plain,(
    $false ),
    inference(simplify,[status(thm)],['30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VAZe9Nhgzg
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:41:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.98/1.16  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.98/1.16  % Solved by: fo/fo7.sh
% 0.98/1.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.98/1.16  % done 1531 iterations in 0.700s
% 0.98/1.16  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.98/1.16  % SZS output start Refutation
% 0.98/1.16  thf(sk_B_type, type, sk_B: $i).
% 0.98/1.16  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.98/1.16  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.98/1.16  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.98/1.16  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.98/1.16  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.98/1.16  thf(sk_A_type, type, sk_A: $i).
% 0.98/1.16  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.98/1.16  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.98/1.16  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.98/1.16  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.98/1.16  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.98/1.16  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.98/1.16  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.98/1.16  thf(t32_subset_1, conjecture,
% 0.98/1.16    (![A:$i,B:$i]:
% 0.98/1.16     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.98/1.16       ( ![C:$i]:
% 0.98/1.16         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.98/1.16           ( ( k7_subset_1 @ A @ B @ C ) =
% 0.98/1.16             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.98/1.16  thf(zf_stmt_0, negated_conjecture,
% 0.98/1.16    (~( ![A:$i,B:$i]:
% 0.98/1.16        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.98/1.16          ( ![C:$i]:
% 0.98/1.16            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.98/1.16              ( ( k7_subset_1 @ A @ B @ C ) =
% 0.98/1.16                ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 0.98/1.16    inference('cnf.neg', [status(esa)], [t32_subset_1])).
% 0.98/1.16  thf('0', plain,
% 0.98/1.16      (((k7_subset_1 @ sk_A @ sk_B @ sk_C_1)
% 0.98/1.16         != (k9_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.98/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.16  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.98/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.16  thf(redefinition_k7_subset_1, axiom,
% 0.98/1.16    (![A:$i,B:$i,C:$i]:
% 0.98/1.16     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.98/1.16       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.98/1.16  thf('2', plain,
% 0.98/1.16      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.98/1.16         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.98/1.16          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k4_xboole_0 @ X22 @ X24)))),
% 0.98/1.16      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.98/1.16  thf('3', plain,
% 0.98/1.16      (![X0 : $i]:
% 0.98/1.16         ((k7_subset_1 @ sk_A @ sk_B @ X0) = (k4_xboole_0 @ sk_B @ X0))),
% 0.98/1.16      inference('sup-', [status(thm)], ['1', '2'])).
% 0.98/1.16  thf('4', plain,
% 0.98/1.16      (((k4_xboole_0 @ sk_B @ sk_C_1)
% 0.98/1.16         != (k9_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.98/1.16      inference('demod', [status(thm)], ['0', '3'])).
% 0.98/1.16  thf('5', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.98/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.16  thf(dt_k3_subset_1, axiom,
% 0.98/1.16    (![A:$i,B:$i]:
% 0.98/1.16     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.98/1.16       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.98/1.16  thf('6', plain,
% 0.98/1.16      (![X19 : $i, X20 : $i]:
% 0.98/1.16         ((m1_subset_1 @ (k3_subset_1 @ X19 @ X20) @ (k1_zfmisc_1 @ X19))
% 0.98/1.16          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.98/1.16      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.98/1.16  thf('7', plain,
% 0.98/1.16      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.98/1.16      inference('sup-', [status(thm)], ['5', '6'])).
% 0.98/1.16  thf(redefinition_k9_subset_1, axiom,
% 0.98/1.16    (![A:$i,B:$i,C:$i]:
% 0.98/1.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.98/1.16       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.98/1.16  thf('8', plain,
% 0.98/1.16      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.98/1.16         (((k9_subset_1 @ X27 @ X25 @ X26) = (k3_xboole_0 @ X25 @ X26))
% 0.98/1.16          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 0.98/1.16      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.98/1.16  thf('9', plain,
% 0.98/1.16      (![X0 : $i]:
% 0.98/1.16         ((k9_subset_1 @ sk_A @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.98/1.16           = (k3_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.98/1.16      inference('sup-', [status(thm)], ['7', '8'])).
% 0.98/1.16  thf('10', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.98/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.16  thf(d2_subset_1, axiom,
% 0.98/1.16    (![A:$i,B:$i]:
% 0.98/1.16     ( ( ( v1_xboole_0 @ A ) =>
% 0.98/1.16         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.98/1.16       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.98/1.16         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.98/1.16  thf('11', plain,
% 0.98/1.16      (![X14 : $i, X15 : $i]:
% 0.98/1.16         (~ (m1_subset_1 @ X14 @ X15)
% 0.98/1.16          | (r2_hidden @ X14 @ X15)
% 0.98/1.16          | (v1_xboole_0 @ X15))),
% 0.98/1.16      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.98/1.16  thf('12', plain,
% 0.98/1.16      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.98/1.16        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.98/1.16      inference('sup-', [status(thm)], ['10', '11'])).
% 0.98/1.16  thf(fc1_subset_1, axiom,
% 0.98/1.16    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.98/1.16  thf('13', plain, (![X21 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X21))),
% 0.98/1.16      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.98/1.16  thf('14', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.98/1.16      inference('clc', [status(thm)], ['12', '13'])).
% 0.98/1.16  thf(d1_zfmisc_1, axiom,
% 0.98/1.16    (![A:$i,B:$i]:
% 0.98/1.16     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.98/1.16       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.98/1.16  thf('15', plain,
% 0.98/1.16      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.98/1.16         (~ (r2_hidden @ X12 @ X11)
% 0.98/1.16          | (r1_tarski @ X12 @ X10)
% 0.98/1.16          | ((X11) != (k1_zfmisc_1 @ X10)))),
% 0.98/1.16      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.98/1.16  thf('16', plain,
% 0.98/1.16      (![X10 : $i, X12 : $i]:
% 0.98/1.16         ((r1_tarski @ X12 @ X10) | ~ (r2_hidden @ X12 @ (k1_zfmisc_1 @ X10)))),
% 0.98/1.16      inference('simplify', [status(thm)], ['15'])).
% 0.98/1.16  thf('17', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.98/1.16      inference('sup-', [status(thm)], ['14', '16'])).
% 0.98/1.16  thf(l32_xboole_1, axiom,
% 0.98/1.16    (![A:$i,B:$i]:
% 0.98/1.16     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.98/1.16  thf('18', plain,
% 0.98/1.16      (![X0 : $i, X2 : $i]:
% 0.98/1.16         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.98/1.16      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.98/1.16  thf('19', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.98/1.16      inference('sup-', [status(thm)], ['17', '18'])).
% 0.98/1.16  thf(t48_xboole_1, axiom,
% 0.98/1.16    (![A:$i,B:$i]:
% 0.98/1.16     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.98/1.16  thf('20', plain,
% 0.98/1.16      (![X4 : $i, X5 : $i]:
% 0.98/1.16         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.98/1.16           = (k3_xboole_0 @ X4 @ X5))),
% 0.98/1.16      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.98/1.16  thf('21', plain,
% 0.98/1.16      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.98/1.16      inference('sup+', [status(thm)], ['19', '20'])).
% 0.98/1.16  thf(t3_boole, axiom,
% 0.98/1.16    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.98/1.16  thf('22', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.98/1.16      inference('cnf', [status(esa)], [t3_boole])).
% 0.98/1.16  thf('23', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.98/1.16      inference('demod', [status(thm)], ['21', '22'])).
% 0.98/1.16  thf('24', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.98/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.16  thf(d5_subset_1, axiom,
% 0.98/1.16    (![A:$i,B:$i]:
% 0.98/1.16     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.98/1.16       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.98/1.16  thf('25', plain,
% 0.98/1.16      (![X17 : $i, X18 : $i]:
% 0.98/1.16         (((k3_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))
% 0.98/1.16          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.98/1.16      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.98/1.16  thf('26', plain,
% 0.98/1.16      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.98/1.16      inference('sup-', [status(thm)], ['24', '25'])).
% 0.98/1.16  thf(t49_xboole_1, axiom,
% 0.98/1.16    (![A:$i,B:$i,C:$i]:
% 0.98/1.16     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.98/1.16       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.98/1.16  thf('27', plain,
% 0.98/1.16      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.98/1.16         ((k3_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X8))
% 0.98/1.16           = (k4_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ X8))),
% 0.98/1.16      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.98/1.16  thf('28', plain,
% 0.98/1.16      (![X0 : $i]:
% 0.98/1.16         ((k3_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.98/1.16           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ sk_A) @ sk_C_1))),
% 0.98/1.16      inference('sup+', [status(thm)], ['26', '27'])).
% 0.98/1.16  thf('29', plain,
% 0.98/1.16      (((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.98/1.16         = (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.98/1.16      inference('sup+', [status(thm)], ['23', '28'])).
% 0.98/1.16  thf('30', plain,
% 0.98/1.16      (((k4_xboole_0 @ sk_B @ sk_C_1) != (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.98/1.16      inference('demod', [status(thm)], ['4', '9', '29'])).
% 0.98/1.16  thf('31', plain, ($false), inference('simplify', [status(thm)], ['30'])).
% 0.98/1.16  
% 0.98/1.16  % SZS output end Refutation
% 0.98/1.16  
% 0.98/1.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
