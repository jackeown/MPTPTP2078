%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jxrDg0sXul

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:14 EST 2020

% Result     : Theorem 9.29s
% Output     : Refutation 9.29s
% Verified   : 
% Statistics : Number of formulae       :   52 (  60 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :  337 ( 489 expanded)
%              Number of equality atoms :   23 (  31 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X17 @ X18 )
        = ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ X15 )
      | ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('16',plain,(
    ! [X21: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('17',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['15','16'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r1_tarski @ X12 @ X10 )
      | ( X11
       != ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('19',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['17','19'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['12','24'])).

thf('26',plain,(
    ( k4_xboole_0 @ sk_B @ sk_C_1 )
 != ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['4','9','25'])).

thf('27',plain,(
    $false ),
    inference(simplify,[status(thm)],['26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jxrDg0sXul
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:26:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 9.29/9.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 9.29/9.48  % Solved by: fo/fo7.sh
% 9.29/9.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.29/9.48  % done 2614 iterations in 9.054s
% 9.29/9.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 9.29/9.48  % SZS output start Refutation
% 9.29/9.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.29/9.48  thf(sk_B_type, type, sk_B: $i).
% 9.29/9.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 9.29/9.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 9.29/9.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 9.29/9.48  thf(sk_A_type, type, sk_A: $i).
% 9.29/9.48  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 9.29/9.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 9.29/9.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 9.29/9.48  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 9.29/9.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 9.29/9.48  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 9.29/9.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 9.29/9.48  thf(t32_subset_1, conjecture,
% 9.29/9.48    (![A:$i,B:$i]:
% 9.29/9.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.29/9.48       ( ![C:$i]:
% 9.29/9.48         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 9.29/9.48           ( ( k7_subset_1 @ A @ B @ C ) =
% 9.29/9.48             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 9.29/9.48  thf(zf_stmt_0, negated_conjecture,
% 9.29/9.48    (~( ![A:$i,B:$i]:
% 9.29/9.48        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.29/9.48          ( ![C:$i]:
% 9.29/9.48            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 9.29/9.48              ( ( k7_subset_1 @ A @ B @ C ) =
% 9.29/9.48                ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 9.29/9.48    inference('cnf.neg', [status(esa)], [t32_subset_1])).
% 9.29/9.48  thf('0', plain,
% 9.29/9.48      (((k7_subset_1 @ sk_A @ sk_B @ sk_C_1)
% 9.29/9.48         != (k9_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 9.29/9.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.29/9.48  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 9.29/9.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.29/9.48  thf(redefinition_k7_subset_1, axiom,
% 9.29/9.48    (![A:$i,B:$i,C:$i]:
% 9.29/9.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.29/9.48       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 9.29/9.48  thf('2', plain,
% 9.29/9.48      (![X22 : $i, X23 : $i, X24 : $i]:
% 9.29/9.48         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 9.29/9.48          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k4_xboole_0 @ X22 @ X24)))),
% 9.29/9.48      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 9.29/9.48  thf('3', plain,
% 9.29/9.48      (![X0 : $i]:
% 9.29/9.48         ((k7_subset_1 @ sk_A @ sk_B @ X0) = (k4_xboole_0 @ sk_B @ X0))),
% 9.29/9.48      inference('sup-', [status(thm)], ['1', '2'])).
% 9.29/9.48  thf('4', plain,
% 9.29/9.48      (((k4_xboole_0 @ sk_B @ sk_C_1)
% 9.29/9.48         != (k9_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 9.29/9.48      inference('demod', [status(thm)], ['0', '3'])).
% 9.29/9.48  thf('5', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 9.29/9.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.29/9.48  thf(dt_k3_subset_1, axiom,
% 9.29/9.48    (![A:$i,B:$i]:
% 9.29/9.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.29/9.48       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 9.29/9.48  thf('6', plain,
% 9.29/9.48      (![X19 : $i, X20 : $i]:
% 9.29/9.48         ((m1_subset_1 @ (k3_subset_1 @ X19 @ X20) @ (k1_zfmisc_1 @ X19))
% 9.29/9.48          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 9.29/9.48      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 9.29/9.48  thf('7', plain,
% 9.29/9.48      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 9.29/9.48      inference('sup-', [status(thm)], ['5', '6'])).
% 9.29/9.48  thf(redefinition_k9_subset_1, axiom,
% 9.29/9.48    (![A:$i,B:$i,C:$i]:
% 9.29/9.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 9.29/9.48       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 9.29/9.48  thf('8', plain,
% 9.29/9.48      (![X25 : $i, X26 : $i, X27 : $i]:
% 9.29/9.48         (((k9_subset_1 @ X27 @ X25 @ X26) = (k3_xboole_0 @ X25 @ X26))
% 9.29/9.48          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 9.29/9.48      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 9.29/9.48  thf('9', plain,
% 9.29/9.48      (![X0 : $i]:
% 9.29/9.48         ((k9_subset_1 @ sk_A @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 9.29/9.48           = (k3_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 9.29/9.48      inference('sup-', [status(thm)], ['7', '8'])).
% 9.29/9.48  thf('10', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 9.29/9.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.29/9.48  thf(d5_subset_1, axiom,
% 9.29/9.48    (![A:$i,B:$i]:
% 9.29/9.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.29/9.48       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 9.29/9.48  thf('11', plain,
% 9.29/9.48      (![X17 : $i, X18 : $i]:
% 9.29/9.48         (((k3_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))
% 9.29/9.48          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 9.29/9.48      inference('cnf', [status(esa)], [d5_subset_1])).
% 9.29/9.48  thf('12', plain,
% 9.29/9.48      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 9.29/9.48      inference('sup-', [status(thm)], ['10', '11'])).
% 9.29/9.48  thf('13', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 9.29/9.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.29/9.48  thf(d2_subset_1, axiom,
% 9.29/9.48    (![A:$i,B:$i]:
% 9.29/9.48     ( ( ( v1_xboole_0 @ A ) =>
% 9.29/9.48         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 9.29/9.48       ( ( ~( v1_xboole_0 @ A ) ) =>
% 9.29/9.48         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 9.29/9.48  thf('14', plain,
% 9.29/9.48      (![X14 : $i, X15 : $i]:
% 9.29/9.48         (~ (m1_subset_1 @ X14 @ X15)
% 9.29/9.48          | (r2_hidden @ X14 @ X15)
% 9.29/9.48          | (v1_xboole_0 @ X15))),
% 9.29/9.48      inference('cnf', [status(esa)], [d2_subset_1])).
% 9.29/9.48  thf('15', plain,
% 9.29/9.48      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 9.29/9.48        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 9.29/9.48      inference('sup-', [status(thm)], ['13', '14'])).
% 9.29/9.48  thf(fc1_subset_1, axiom,
% 9.29/9.48    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 9.29/9.48  thf('16', plain, (![X21 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X21))),
% 9.29/9.48      inference('cnf', [status(esa)], [fc1_subset_1])).
% 9.29/9.48  thf('17', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 9.29/9.48      inference('clc', [status(thm)], ['15', '16'])).
% 9.29/9.48  thf(d1_zfmisc_1, axiom,
% 9.29/9.48    (![A:$i,B:$i]:
% 9.29/9.48     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 9.29/9.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 9.29/9.48  thf('18', plain,
% 9.29/9.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 9.29/9.48         (~ (r2_hidden @ X12 @ X11)
% 9.29/9.48          | (r1_tarski @ X12 @ X10)
% 9.29/9.48          | ((X11) != (k1_zfmisc_1 @ X10)))),
% 9.29/9.48      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 9.29/9.48  thf('19', plain,
% 9.29/9.48      (![X10 : $i, X12 : $i]:
% 9.29/9.48         ((r1_tarski @ X12 @ X10) | ~ (r2_hidden @ X12 @ (k1_zfmisc_1 @ X10)))),
% 9.29/9.48      inference('simplify', [status(thm)], ['18'])).
% 9.29/9.48  thf('20', plain, ((r1_tarski @ sk_B @ sk_A)),
% 9.29/9.48      inference('sup-', [status(thm)], ['17', '19'])).
% 9.29/9.48  thf(t28_xboole_1, axiom,
% 9.29/9.48    (![A:$i,B:$i]:
% 9.29/9.48     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 9.29/9.48  thf('21', plain,
% 9.29/9.48      (![X2 : $i, X3 : $i]:
% 9.29/9.48         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 9.29/9.48      inference('cnf', [status(esa)], [t28_xboole_1])).
% 9.29/9.48  thf('22', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 9.29/9.48      inference('sup-', [status(thm)], ['20', '21'])).
% 9.29/9.48  thf(t49_xboole_1, axiom,
% 9.29/9.48    (![A:$i,B:$i,C:$i]:
% 9.29/9.48     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 9.29/9.48       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 9.29/9.48  thf('23', plain,
% 9.29/9.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 9.29/9.48         ((k3_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X8))
% 9.29/9.48           = (k4_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ X8))),
% 9.29/9.48      inference('cnf', [status(esa)], [t49_xboole_1])).
% 9.29/9.48  thf('24', plain,
% 9.29/9.48      (![X0 : $i]:
% 9.29/9.48         ((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ X0))
% 9.29/9.48           = (k4_xboole_0 @ sk_B @ X0))),
% 9.29/9.48      inference('sup+', [status(thm)], ['22', '23'])).
% 9.29/9.48  thf('25', plain,
% 9.29/9.48      (((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))
% 9.29/9.48         = (k4_xboole_0 @ sk_B @ sk_C_1))),
% 9.29/9.48      inference('sup+', [status(thm)], ['12', '24'])).
% 9.29/9.48  thf('26', plain,
% 9.29/9.48      (((k4_xboole_0 @ sk_B @ sk_C_1) != (k4_xboole_0 @ sk_B @ sk_C_1))),
% 9.29/9.48      inference('demod', [status(thm)], ['4', '9', '25'])).
% 9.29/9.48  thf('27', plain, ($false), inference('simplify', [status(thm)], ['26'])).
% 9.29/9.48  
% 9.29/9.48  % SZS output end Refutation
% 9.29/9.48  
% 9.29/9.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
