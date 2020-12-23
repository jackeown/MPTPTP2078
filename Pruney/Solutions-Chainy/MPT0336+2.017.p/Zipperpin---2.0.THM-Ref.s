%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.g3jPv0h7hW

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:22 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   56 (  68 expanded)
%              Number of leaves         :   21 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  341 ( 505 expanded)
%              Number of equality atoms :   21 (  24 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t149_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ C )
        & ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ C )
          & ( r1_xboole_0 @ C @ B ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t149_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('3',plain,(
    ! [X37: $i,X38: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X37 ) @ X38 )
      | ( r2_hidden @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','10','11'])).

thf('13',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','12'])).

thf('14',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_xboole_0 @ X19 @ X20 )
      | ( r1_xboole_0 @ X19 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r2_hidden @ sk_D @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('18',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['13','20'])).

thf('22',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('24',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('25',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_xboole_0 @ X22 @ X23 )
      | ( ( k3_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) )
        = ( k3_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','28'])).

thf('30',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('32',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['2','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.g3jPv0h7hW
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:40:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.60/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.77  % Solved by: fo/fo7.sh
% 0.60/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.77  % done 902 iterations in 0.298s
% 0.60/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.77  % SZS output start Refutation
% 0.60/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.60/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.77  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.60/0.77  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.60/0.77  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.60/0.77  thf(sk_D_type, type, sk_D: $i).
% 0.60/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.77  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.60/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.77  thf(t149_zfmisc_1, conjecture,
% 0.60/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.77     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.60/0.77         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.60/0.77       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.60/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.77    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.77        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.60/0.77            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.60/0.77          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 0.60/0.77    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 0.60/0.77  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf(commutativity_k2_xboole_0, axiom,
% 0.60/0.77    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.60/0.77  thf('1', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.60/0.77      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.60/0.77  thf('2', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_B)),
% 0.60/0.77      inference('demod', [status(thm)], ['0', '1'])).
% 0.60/0.77  thf(l27_zfmisc_1, axiom,
% 0.60/0.77    (![A:$i,B:$i]:
% 0.60/0.77     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.60/0.77  thf('3', plain,
% 0.60/0.77      (![X37 : $i, X38 : $i]:
% 0.60/0.77         ((r1_xboole_0 @ (k1_tarski @ X37) @ X38) | (r2_hidden @ X37 @ X38))),
% 0.60/0.77      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.60/0.77  thf(d7_xboole_0, axiom,
% 0.60/0.77    (![A:$i,B:$i]:
% 0.60/0.77     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.60/0.77       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.60/0.77  thf('4', plain,
% 0.60/0.77      (![X4 : $i, X5 : $i]:
% 0.60/0.77         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.60/0.77      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.60/0.77  thf('5', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((r2_hidden @ X1 @ X0)
% 0.60/0.77          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['3', '4'])).
% 0.60/0.77  thf('6', plain,
% 0.60/0.77      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf(t28_xboole_1, axiom,
% 0.60/0.77    (![A:$i,B:$i]:
% 0.60/0.77     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.60/0.77  thf('7', plain,
% 0.60/0.77      (![X15 : $i, X16 : $i]:
% 0.60/0.77         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.60/0.77      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.60/0.77  thf('8', plain,
% 0.60/0.77      (((k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))
% 0.60/0.77         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.60/0.77      inference('sup-', [status(thm)], ['6', '7'])).
% 0.60/0.77  thf(commutativity_k3_xboole_0, axiom,
% 0.60/0.77    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.60/0.77  thf('9', plain,
% 0.60/0.77      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.60/0.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.60/0.77  thf('10', plain,
% 0.60/0.77      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.60/0.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.60/0.77  thf('11', plain,
% 0.60/0.77      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.60/0.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.60/0.77  thf('12', plain,
% 0.60/0.77      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.60/0.77         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.60/0.77      inference('demod', [status(thm)], ['8', '9', '10', '11'])).
% 0.60/0.77  thf('13', plain,
% 0.60/0.77      ((((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))
% 0.60/0.77        | (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.60/0.77      inference('sup+', [status(thm)], ['5', '12'])).
% 0.60/0.77  thf('14', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf(t74_xboole_1, axiom,
% 0.60/0.77    (![A:$i,B:$i,C:$i]:
% 0.60/0.77     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 0.60/0.77          ( r1_xboole_0 @ A @ B ) ) ))).
% 0.60/0.77  thf('15', plain,
% 0.60/0.77      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.60/0.77         (~ (r1_xboole_0 @ X19 @ X20)
% 0.60/0.77          | (r1_xboole_0 @ X19 @ (k3_xboole_0 @ X20 @ X21)))),
% 0.60/0.77      inference('cnf', [status(esa)], [t74_xboole_1])).
% 0.60/0.77  thf('16', plain,
% 0.60/0.77      (![X0 : $i]: (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_B @ X0))),
% 0.60/0.77      inference('sup-', [status(thm)], ['14', '15'])).
% 0.60/0.77  thf('17', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf(t3_xboole_0, axiom,
% 0.60/0.77    (![A:$i,B:$i]:
% 0.60/0.77     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.60/0.77            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.60/0.77       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.60/0.77            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.60/0.77  thf('18', plain,
% 0.60/0.77      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.60/0.77         (~ (r2_hidden @ X11 @ X9)
% 0.60/0.77          | ~ (r2_hidden @ X11 @ X12)
% 0.60/0.77          | ~ (r1_xboole_0 @ X9 @ X12))),
% 0.60/0.77      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.60/0.77  thf('19', plain,
% 0.60/0.77      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 0.60/0.77      inference('sup-', [status(thm)], ['17', '18'])).
% 0.60/0.77  thf('20', plain,
% 0.60/0.77      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ X0))),
% 0.60/0.77      inference('sup-', [status(thm)], ['16', '19'])).
% 0.60/0.77  thf('21', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.60/0.77      inference('clc', [status(thm)], ['13', '20'])).
% 0.60/0.77  thf('22', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf(symmetry_r1_xboole_0, axiom,
% 0.60/0.77    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.60/0.77  thf('23', plain,
% 0.60/0.77      (![X7 : $i, X8 : $i]:
% 0.60/0.77         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 0.60/0.77      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.60/0.77  thf('24', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.60/0.77      inference('sup-', [status(thm)], ['22', '23'])).
% 0.60/0.77  thf(t78_xboole_1, axiom,
% 0.60/0.77    (![A:$i,B:$i,C:$i]:
% 0.60/0.77     ( ( r1_xboole_0 @ A @ B ) =>
% 0.60/0.77       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.60/0.77         ( k3_xboole_0 @ A @ C ) ) ))).
% 0.60/0.77  thf('25', plain,
% 0.60/0.77      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.60/0.77         (~ (r1_xboole_0 @ X22 @ X23)
% 0.60/0.77          | ((k3_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24))
% 0.60/0.77              = (k3_xboole_0 @ X22 @ X24)))),
% 0.60/0.77      inference('cnf', [status(esa)], [t78_xboole_1])).
% 0.60/0.77  thf('26', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ X0))
% 0.60/0.77           = (k3_xboole_0 @ sk_B @ X0))),
% 0.60/0.77      inference('sup-', [status(thm)], ['24', '25'])).
% 0.60/0.77  thf('27', plain,
% 0.60/0.77      (![X4 : $i, X6 : $i]:
% 0.60/0.77         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 0.60/0.77      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.60/0.77  thf('28', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         (((k3_xboole_0 @ sk_B @ X0) != (k1_xboole_0))
% 0.60/0.77          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ X0)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['26', '27'])).
% 0.60/0.77  thf('29', plain,
% 0.60/0.77      ((((k1_xboole_0) != (k1_xboole_0))
% 0.60/0.77        | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ sk_A)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['21', '28'])).
% 0.60/0.77  thf('30', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ sk_A))),
% 0.60/0.77      inference('simplify', [status(thm)], ['29'])).
% 0.60/0.77  thf('31', plain,
% 0.60/0.77      (![X7 : $i, X8 : $i]:
% 0.60/0.77         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 0.60/0.77      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.60/0.77  thf('32', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_B)),
% 0.60/0.77      inference('sup-', [status(thm)], ['30', '31'])).
% 0.60/0.77  thf('33', plain, ($false), inference('demod', [status(thm)], ['2', '32'])).
% 0.60/0.77  
% 0.60/0.77  % SZS output end Refutation
% 0.60/0.77  
% 0.60/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
