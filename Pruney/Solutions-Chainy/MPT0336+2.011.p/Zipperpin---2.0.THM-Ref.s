%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5dJ7qFoSBT

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:21 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :   61 (  74 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  373 ( 547 expanded)
%              Number of equality atoms :   26 (  31 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X40: $i,X41: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X40 ) @ X41 )
      | ( r2_hidden @ X40 @ X41 ) ) ),
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

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['10','11'])).

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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_xboole_0 @ X21 @ X22 )
      | ( r1_xboole_0 @ X21 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
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
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
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

thf('23',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('24',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('28',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference(simplify,[status(thm)],['28'])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('30',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_xboole_0 @ X24 @ X25 )
      | ( ( k3_xboole_0 @ X24 @ ( k2_xboole_0 @ X25 @ X26 ) )
        = ( k3_xboole_0 @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','33'])).

thf('35',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['34'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('37',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['2','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5dJ7qFoSBT
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:02:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.05/1.26  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.05/1.26  % Solved by: fo/fo7.sh
% 1.05/1.26  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.26  % done 2019 iterations in 0.820s
% 1.05/1.26  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.05/1.26  % SZS output start Refutation
% 1.05/1.26  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.05/1.26  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.05/1.26  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.05/1.26  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.05/1.26  thf(sk_B_type, type, sk_B: $i).
% 1.05/1.26  thf(sk_D_type, type, sk_D: $i).
% 1.05/1.26  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.05/1.26  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.05/1.26  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.26  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.05/1.26  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.05/1.26  thf(t149_zfmisc_1, conjecture,
% 1.05/1.26    (![A:$i,B:$i,C:$i,D:$i]:
% 1.05/1.26     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.05/1.26         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.05/1.26       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.05/1.26  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.26    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.05/1.26        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.05/1.26            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.05/1.26          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 1.05/1.26    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 1.05/1.26  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf(commutativity_k2_xboole_0, axiom,
% 1.05/1.26    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.05/1.26  thf('1', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.05/1.26      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.05/1.26  thf('2', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_B)),
% 1.05/1.26      inference('demod', [status(thm)], ['0', '1'])).
% 1.05/1.26  thf(l27_zfmisc_1, axiom,
% 1.05/1.26    (![A:$i,B:$i]:
% 1.05/1.26     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.05/1.26  thf('3', plain,
% 1.05/1.26      (![X40 : $i, X41 : $i]:
% 1.05/1.26         ((r1_xboole_0 @ (k1_tarski @ X40) @ X41) | (r2_hidden @ X40 @ X41))),
% 1.05/1.26      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.05/1.26  thf(d7_xboole_0, axiom,
% 1.05/1.26    (![A:$i,B:$i]:
% 1.05/1.26     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.05/1.26       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.05/1.26  thf('4', plain,
% 1.05/1.26      (![X4 : $i, X5 : $i]:
% 1.05/1.26         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 1.05/1.26      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.05/1.26  thf('5', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         ((r2_hidden @ X1 @ X0)
% 1.05/1.26          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['3', '4'])).
% 1.05/1.26  thf('6', plain,
% 1.05/1.26      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf(commutativity_k3_xboole_0, axiom,
% 1.05/1.26    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.05/1.26  thf('7', plain,
% 1.05/1.26      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.05/1.26      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.05/1.26  thf('8', plain,
% 1.05/1.26      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 1.05/1.26      inference('demod', [status(thm)], ['6', '7'])).
% 1.05/1.26  thf(t28_xboole_1, axiom,
% 1.05/1.26    (![A:$i,B:$i]:
% 1.05/1.26     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.05/1.26  thf('9', plain,
% 1.05/1.26      (![X19 : $i, X20 : $i]:
% 1.05/1.26         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 1.05/1.26      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.05/1.26  thf('10', plain,
% 1.05/1.26      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))
% 1.05/1.26         = (k3_xboole_0 @ sk_B @ sk_A))),
% 1.05/1.26      inference('sup-', [status(thm)], ['8', '9'])).
% 1.05/1.26  thf('11', plain,
% 1.05/1.26      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.05/1.26      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.05/1.26  thf('12', plain,
% 1.05/1.26      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A))
% 1.05/1.26         = (k3_xboole_0 @ sk_B @ sk_A))),
% 1.05/1.26      inference('demod', [status(thm)], ['10', '11'])).
% 1.05/1.26  thf('13', plain,
% 1.05/1.26      ((((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))
% 1.05/1.26        | (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 1.05/1.26      inference('sup+', [status(thm)], ['5', '12'])).
% 1.05/1.26  thf('14', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf(t74_xboole_1, axiom,
% 1.05/1.26    (![A:$i,B:$i,C:$i]:
% 1.05/1.26     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 1.05/1.26          ( r1_xboole_0 @ A @ B ) ) ))).
% 1.05/1.26  thf('15', plain,
% 1.05/1.26      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.05/1.26         (~ (r1_xboole_0 @ X21 @ X22)
% 1.05/1.26          | (r1_xboole_0 @ X21 @ (k3_xboole_0 @ X22 @ X23)))),
% 1.05/1.26      inference('cnf', [status(esa)], [t74_xboole_1])).
% 1.05/1.26  thf('16', plain,
% 1.05/1.26      (![X0 : $i]: (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_B @ X0))),
% 1.05/1.26      inference('sup-', [status(thm)], ['14', '15'])).
% 1.05/1.26  thf('17', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf(t3_xboole_0, axiom,
% 1.05/1.26    (![A:$i,B:$i]:
% 1.05/1.26     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.05/1.26            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.05/1.26       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.05/1.26            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.05/1.26  thf('18', plain,
% 1.05/1.26      (![X10 : $i, X12 : $i, X13 : $i]:
% 1.05/1.26         (~ (r2_hidden @ X12 @ X10)
% 1.05/1.26          | ~ (r2_hidden @ X12 @ X13)
% 1.05/1.26          | ~ (r1_xboole_0 @ X10 @ X13))),
% 1.05/1.26      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.05/1.26  thf('19', plain,
% 1.05/1.26      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 1.05/1.26      inference('sup-', [status(thm)], ['17', '18'])).
% 1.05/1.26  thf('20', plain,
% 1.05/1.26      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ X0))),
% 1.05/1.26      inference('sup-', [status(thm)], ['16', '19'])).
% 1.05/1.26  thf('21', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 1.05/1.26      inference('clc', [status(thm)], ['13', '20'])).
% 1.05/1.26  thf('22', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('23', plain,
% 1.05/1.26      (![X4 : $i, X5 : $i]:
% 1.05/1.26         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 1.05/1.26      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.05/1.26  thf('24', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B) = (k1_xboole_0))),
% 1.05/1.26      inference('sup-', [status(thm)], ['22', '23'])).
% 1.05/1.26  thf('25', plain,
% 1.05/1.26      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.05/1.26      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.05/1.26  thf('26', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 1.05/1.26      inference('demod', [status(thm)], ['24', '25'])).
% 1.05/1.26  thf('27', plain,
% 1.05/1.26      (![X4 : $i, X6 : $i]:
% 1.05/1.26         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 1.05/1.26      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.05/1.26  thf('28', plain,
% 1.05/1.26      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_C_1))),
% 1.05/1.26      inference('sup-', [status(thm)], ['26', '27'])).
% 1.05/1.26  thf('29', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 1.05/1.26      inference('simplify', [status(thm)], ['28'])).
% 1.05/1.26  thf(t78_xboole_1, axiom,
% 1.05/1.26    (![A:$i,B:$i,C:$i]:
% 1.05/1.26     ( ( r1_xboole_0 @ A @ B ) =>
% 1.05/1.26       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 1.05/1.26         ( k3_xboole_0 @ A @ C ) ) ))).
% 1.05/1.26  thf('30', plain,
% 1.05/1.26      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.05/1.26         (~ (r1_xboole_0 @ X24 @ X25)
% 1.05/1.26          | ((k3_xboole_0 @ X24 @ (k2_xboole_0 @ X25 @ X26))
% 1.05/1.26              = (k3_xboole_0 @ X24 @ X26)))),
% 1.05/1.26      inference('cnf', [status(esa)], [t78_xboole_1])).
% 1.05/1.26  thf('31', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ X0))
% 1.05/1.26           = (k3_xboole_0 @ sk_B @ X0))),
% 1.05/1.26      inference('sup-', [status(thm)], ['29', '30'])).
% 1.05/1.26  thf('32', plain,
% 1.05/1.26      (![X4 : $i, X6 : $i]:
% 1.05/1.26         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 1.05/1.26      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.05/1.26  thf('33', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (((k3_xboole_0 @ sk_B @ X0) != (k1_xboole_0))
% 1.05/1.26          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ X0)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['31', '32'])).
% 1.05/1.26  thf('34', plain,
% 1.05/1.26      ((((k1_xboole_0) != (k1_xboole_0))
% 1.05/1.26        | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ sk_A)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['21', '33'])).
% 1.05/1.26  thf('35', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ sk_A))),
% 1.05/1.26      inference('simplify', [status(thm)], ['34'])).
% 1.05/1.26  thf(symmetry_r1_xboole_0, axiom,
% 1.05/1.26    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.05/1.26  thf('36', plain,
% 1.05/1.26      (![X8 : $i, X9 : $i]:
% 1.05/1.26         ((r1_xboole_0 @ X8 @ X9) | ~ (r1_xboole_0 @ X9 @ X8))),
% 1.05/1.26      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.05/1.26  thf('37', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_B)),
% 1.05/1.26      inference('sup-', [status(thm)], ['35', '36'])).
% 1.05/1.26  thf('38', plain, ($false), inference('demod', [status(thm)], ['2', '37'])).
% 1.05/1.26  
% 1.05/1.26  % SZS output end Refutation
% 1.05/1.26  
% 1.05/1.27  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
