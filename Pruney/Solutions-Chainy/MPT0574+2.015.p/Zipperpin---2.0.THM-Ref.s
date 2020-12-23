%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uYzYoa24PE

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 (  46 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :  218 ( 274 expanded)
%              Number of equality atoms :   19 (  20 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t178_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t178_relat_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('2',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('4',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('5',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('6',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X9 @ X8 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X10 @ X11 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X10 @ X11 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(t175_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k10_relat_1 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X12 @ X13 ) @ ( k10_relat_1 @ X12 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_A ) @ ( k10_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['18','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uYzYoa24PE
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:10:32 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 69 iterations in 0.027s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(t178_relat_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ C ) =>
% 0.21/0.49       ( ( r1_tarski @ A @ B ) =>
% 0.21/0.49         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.49        ( ( v1_relat_1 @ C ) =>
% 0.21/0.49          ( ( r1_tarski @ A @ B ) =>
% 0.21/0.49            ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t178_relat_1])).
% 0.21/0.49  thf('0', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(l32_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X0 : $i, X2 : $i]:
% 0.21/0.49         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.49  thf('2', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf(t39_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i]:
% 0.21/0.49         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 0.21/0.49           = (k2_xboole_0 @ X4 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (((k2_xboole_0 @ sk_B @ k1_xboole_0) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.49      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf(t1_boole, axiom,
% 0.21/0.49    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.49  thf('5', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.49  thf('6', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf(commutativity_k2_tarski, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i]: ((k2_tarski @ X9 @ X8) = (k2_tarski @ X8 @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.49  thf(l51_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i]:
% 0.21/0.49         ((k3_tarski @ (k2_tarski @ X10 @ X11)) = (k2_xboole_0 @ X10 @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.49      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i]:
% 0.21/0.49         ((k3_tarski @ (k2_tarski @ X10 @ X11)) = (k2_xboole_0 @ X10 @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.49      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf('12', plain, (((sk_B) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['6', '11'])).
% 0.21/0.49  thf(t175_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ C ) =>
% 0.21/0.49       ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.21/0.49         ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.49         (((k10_relat_1 @ X12 @ (k2_xboole_0 @ X13 @ X14))
% 0.21/0.49            = (k2_xboole_0 @ (k10_relat_1 @ X12 @ X13) @ 
% 0.21/0.49               (k10_relat_1 @ X12 @ X14)))
% 0.21/0.49          | ~ (v1_relat_1 @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [t175_relat_1])).
% 0.21/0.49  thf(t7_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((r1_tarski @ (k10_relat_1 @ X2 @ X1) @ 
% 0.21/0.49           (k10_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.21/0.49          | ~ (v1_relat_1 @ X2))),
% 0.21/0.49      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r1_tarski @ (k10_relat_1 @ X0 @ sk_A) @ (k10_relat_1 @ X0 @ sk_B))
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['12', '15'])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (~ (r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('18', plain, (~ (v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.49  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('20', plain, ($false), inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
