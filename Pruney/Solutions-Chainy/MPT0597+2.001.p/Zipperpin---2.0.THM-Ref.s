%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A17UaCBNaQ

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 (  63 expanded)
%              Number of leaves         :   19 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  244 ( 483 expanded)
%              Number of equality atoms :   27 (  54 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t101_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X1 @ X2 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t101_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k5_xboole_0 @ X0 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('simplify_reflect+',[status(thm)],['6','7'])).

thf(t162_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf('9',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X24 @ X25 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X26 @ X25 ) @ X24 )
        = ( k9_relat_1 @ X26 @ X24 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 )
        = ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t201_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( ( k7_relat_1 @ B @ A )
              = ( k7_relat_1 @ C @ A ) )
           => ( ( k9_relat_1 @ B @ A )
              = ( k9_relat_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ! [C: $i] :
            ( ( v1_relat_1 @ C )
           => ( ( ( k7_relat_1 @ B @ A )
                = ( k7_relat_1 @ C @ A ) )
             => ( ( k9_relat_1 @ B @ A )
                = ( k9_relat_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t201_relat_1])).

thf('11',plain,
    ( ( k7_relat_1 @ sk_B @ sk_A )
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 )
        = ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('13',plain,
    ( ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ( k9_relat_1 @ sk_B @ sk_A )
 != ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A17UaCBNaQ
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:56:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 76 iterations in 0.034s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(idempotence_k2_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.49  thf('0', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.21/0.49  thf(t101_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( k5_xboole_0 @ A @ B ) =
% 0.21/0.49       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X1 : $i, X2 : $i]:
% 0.21/0.49         ((k5_xboole_0 @ X1 @ X2)
% 0.21/0.49           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t101_xboole_1])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((k5_xboole_0 @ X0 @ X0)
% 0.21/0.49           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf(t47_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i]:
% 0.21/0.49         ((k4_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7))
% 0.21/0.49           = (k4_xboole_0 @ X6 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf(t37_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i]:
% 0.21/0.49         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k5_xboole_0 @ X0 @ X0) != (k1_xboole_0)) | (r1_tarski @ X0 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf(t92_xboole_1, axiom,
% 0.21/0.49    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.49  thf('7', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.21/0.49  thf('8', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.49      inference('simplify_reflect+', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf(t162_relat_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ![B:$i,C:$i]:
% 0.21/0.49         ( ( r1_tarski @ B @ C ) =>
% 0.21/0.49           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.21/0.49             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.49         (~ (r1_tarski @ X24 @ X25)
% 0.21/0.49          | ((k9_relat_1 @ (k7_relat_1 @ X26 @ X25) @ X24)
% 0.21/0.49              = (k9_relat_1 @ X26 @ X24))
% 0.21/0.49          | ~ (v1_relat_1 @ X26))),
% 0.21/0.49      inference('cnf', [status(esa)], [t162_relat_1])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X1)
% 0.21/0.49          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0)
% 0.21/0.49              = (k9_relat_1 @ X1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf(t201_relat_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ B ) =>
% 0.21/0.49       ( ![C:$i]:
% 0.21/0.49         ( ( v1_relat_1 @ C ) =>
% 0.21/0.49           ( ( ( k7_relat_1 @ B @ A ) = ( k7_relat_1 @ C @ A ) ) =>
% 0.21/0.49             ( ( k9_relat_1 @ B @ A ) = ( k9_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i]:
% 0.21/0.49        ( ( v1_relat_1 @ B ) =>
% 0.21/0.49          ( ![C:$i]:
% 0.21/0.49            ( ( v1_relat_1 @ C ) =>
% 0.21/0.49              ( ( ( k7_relat_1 @ B @ A ) = ( k7_relat_1 @ C @ A ) ) =>
% 0.21/0.49                ( ( k9_relat_1 @ B @ A ) = ( k9_relat_1 @ C @ A ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t201_relat_1])).
% 0.21/0.49  thf('11', plain, (((k7_relat_1 @ sk_B @ sk_A) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X1)
% 0.21/0.49          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0)
% 0.21/0.49              = (k9_relat_1 @ X1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      ((((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.21/0.49          = (k9_relat_1 @ sk_C @ sk_A))
% 0.21/0.49        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.49      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('14', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.21/0.49         = (k9_relat_1 @ sk_C @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      ((((k9_relat_1 @ sk_B @ sk_A) = (k9_relat_1 @ sk_C @ sk_A))
% 0.21/0.49        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.49      inference('sup+', [status(thm)], ['10', '15'])).
% 0.21/0.49  thf('17', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('18', plain, (((k9_relat_1 @ sk_B @ sk_A) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (((k9_relat_1 @ sk_B @ sk_A) != (k9_relat_1 @ sk_C @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('20', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
