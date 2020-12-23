%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iq8p9hLAdE

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:28 EST 2020

% Result     : Theorem 5.63s
% Output     : Refutation 5.63s
% Verified   : 
% Statistics : Number of formulae       :   65 (  83 expanded)
%              Number of leaves         :   25 (  35 expanded)
%              Depth                    :   18
%              Number of atoms          :  376 ( 580 expanded)
%              Number of equality atoms :   35 (  44 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('9',plain,(
    ! [X47: $i,X48: $i] :
      ( ( X48
        = ( k1_tarski @ X47 ) )
      | ( X48 = k1_xboole_0 )
      | ~ ( r1_tarski @ X48 @ ( k1_tarski @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('10',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B @ sk_A )
      = ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('16',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['14','15'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X7 @ X9 )
      | ~ ( r1_tarski @ X7 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( r1_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_C )
    | ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','19'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('21',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('22',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X52 @ X53 ) @ X54 )
      | ~ ( r2_hidden @ X52 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    r2_hidden @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('28',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['28'])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('30',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_xboole_0 @ X16 @ X17 )
      | ( ( k3_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
        = ( k3_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','35'])).

thf('37',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C ) @ sk_B ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['0','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iq8p9hLAdE
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:40:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.63/5.85  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.63/5.85  % Solved by: fo/fo7.sh
% 5.63/5.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.63/5.85  % done 1959 iterations in 5.381s
% 5.63/5.85  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.63/5.85  % SZS output start Refutation
% 5.63/5.85  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 5.63/5.85  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.63/5.85  thf(sk_D_type, type, sk_D: $i).
% 5.63/5.85  thf(sk_C_type, type, sk_C: $i).
% 5.63/5.85  thf(sk_B_type, type, sk_B: $i).
% 5.63/5.85  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.63/5.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.63/5.85  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 5.63/5.85  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 5.63/5.85  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.63/5.85  thf(sk_A_type, type, sk_A: $i).
% 5.63/5.85  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.63/5.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.63/5.85  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 5.63/5.85  thf(t149_zfmisc_1, conjecture,
% 5.63/5.85    (![A:$i,B:$i,C:$i,D:$i]:
% 5.63/5.85     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 5.63/5.85         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 5.63/5.85       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 5.63/5.85  thf(zf_stmt_0, negated_conjecture,
% 5.63/5.85    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 5.63/5.85        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 5.63/5.85            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 5.63/5.85          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 5.63/5.85    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 5.63/5.85  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 5.63/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.63/5.85  thf('1', plain, ((r1_xboole_0 @ sk_C @ sk_B)),
% 5.63/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.63/5.85  thf(d7_xboole_0, axiom,
% 5.63/5.85    (![A:$i,B:$i]:
% 5.63/5.85     ( ( r1_xboole_0 @ A @ B ) <=>
% 5.63/5.85       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 5.63/5.85  thf('2', plain,
% 5.63/5.85      (![X2 : $i, X3 : $i]:
% 5.63/5.85         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 5.63/5.85      inference('cnf', [status(esa)], [d7_xboole_0])).
% 5.63/5.85  thf('3', plain, (((k3_xboole_0 @ sk_C @ sk_B) = (k1_xboole_0))),
% 5.63/5.85      inference('sup-', [status(thm)], ['1', '2'])).
% 5.63/5.85  thf(commutativity_k3_xboole_0, axiom,
% 5.63/5.85    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 5.63/5.85  thf('4', plain,
% 5.63/5.85      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.63/5.85      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.63/5.85  thf('5', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 5.63/5.85      inference('demod', [status(thm)], ['3', '4'])).
% 5.63/5.85  thf('6', plain,
% 5.63/5.85      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 5.63/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.63/5.85  thf('7', plain,
% 5.63/5.85      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.63/5.85      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.63/5.85  thf('8', plain,
% 5.63/5.85      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 5.63/5.85      inference('demod', [status(thm)], ['6', '7'])).
% 5.63/5.85  thf(l3_zfmisc_1, axiom,
% 5.63/5.85    (![A:$i,B:$i]:
% 5.63/5.85     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 5.63/5.85       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 5.63/5.85  thf('9', plain,
% 5.63/5.85      (![X47 : $i, X48 : $i]:
% 5.63/5.85         (((X48) = (k1_tarski @ X47))
% 5.63/5.85          | ((X48) = (k1_xboole_0))
% 5.63/5.85          | ~ (r1_tarski @ X48 @ (k1_tarski @ X47)))),
% 5.63/5.85      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 5.63/5.85  thf('10', plain,
% 5.63/5.85      ((((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))
% 5.63/5.85        | ((k3_xboole_0 @ sk_B @ sk_A) = (k1_tarski @ sk_D)))),
% 5.63/5.85      inference('sup-', [status(thm)], ['8', '9'])).
% 5.63/5.85  thf(t17_xboole_1, axiom,
% 5.63/5.85    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 5.63/5.85  thf('11', plain,
% 5.63/5.85      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 5.63/5.85      inference('cnf', [status(esa)], [t17_xboole_1])).
% 5.63/5.85  thf('12', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 5.63/5.85      inference('demod', [status(thm)], ['3', '4'])).
% 5.63/5.85  thf(t100_xboole_1, axiom,
% 5.63/5.85    (![A:$i,B:$i]:
% 5.63/5.85     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 5.63/5.85  thf('13', plain,
% 5.63/5.85      (![X5 : $i, X6 : $i]:
% 5.63/5.85         ((k4_xboole_0 @ X5 @ X6)
% 5.63/5.85           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 5.63/5.85      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.63/5.85  thf('14', plain,
% 5.63/5.85      (((k4_xboole_0 @ sk_B @ sk_C) = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 5.63/5.85      inference('sup+', [status(thm)], ['12', '13'])).
% 5.63/5.85  thf(t5_boole, axiom,
% 5.63/5.85    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 5.63/5.85  thf('15', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 5.63/5.85      inference('cnf', [status(esa)], [t5_boole])).
% 5.63/5.85  thf('16', plain, (((k4_xboole_0 @ sk_B @ sk_C) = (sk_B))),
% 5.63/5.85      inference('demod', [status(thm)], ['14', '15'])).
% 5.63/5.85  thf(t106_xboole_1, axiom,
% 5.63/5.85    (![A:$i,B:$i,C:$i]:
% 5.63/5.85     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 5.63/5.85       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 5.63/5.85  thf('17', plain,
% 5.63/5.85      (![X7 : $i, X8 : $i, X9 : $i]:
% 5.63/5.85         ((r1_xboole_0 @ X7 @ X9)
% 5.63/5.85          | ~ (r1_tarski @ X7 @ (k4_xboole_0 @ X8 @ X9)))),
% 5.63/5.85      inference('cnf', [status(esa)], [t106_xboole_1])).
% 5.63/5.85  thf('18', plain,
% 5.63/5.85      (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_B) | (r1_xboole_0 @ X0 @ sk_C))),
% 5.63/5.85      inference('sup-', [status(thm)], ['16', '17'])).
% 5.63/5.85  thf('19', plain,
% 5.63/5.85      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ sk_C)),
% 5.63/5.85      inference('sup-', [status(thm)], ['11', '18'])).
% 5.63/5.85  thf('20', plain,
% 5.63/5.85      (((r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_C)
% 5.63/5.85        | ((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 5.63/5.85      inference('sup+', [status(thm)], ['10', '19'])).
% 5.63/5.85  thf(t69_enumset1, axiom,
% 5.63/5.85    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 5.63/5.85  thf('21', plain,
% 5.63/5.85      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 5.63/5.85      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.63/5.85  thf(t55_zfmisc_1, axiom,
% 5.63/5.85    (![A:$i,B:$i,C:$i]:
% 5.63/5.85     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 5.63/5.85  thf('22', plain,
% 5.63/5.85      (![X52 : $i, X53 : $i, X54 : $i]:
% 5.63/5.85         (~ (r1_xboole_0 @ (k2_tarski @ X52 @ X53) @ X54)
% 5.63/5.85          | ~ (r2_hidden @ X52 @ X54))),
% 5.63/5.85      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 5.63/5.85  thf('23', plain,
% 5.63/5.85      (![X0 : $i, X1 : $i]:
% 5.63/5.85         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 5.63/5.85      inference('sup-', [status(thm)], ['21', '22'])).
% 5.63/5.85  thf('24', plain,
% 5.63/5.85      ((((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))
% 5.63/5.85        | ~ (r2_hidden @ sk_D @ sk_C))),
% 5.63/5.85      inference('sup-', [status(thm)], ['20', '23'])).
% 5.63/5.85  thf('25', plain, ((r2_hidden @ sk_D @ sk_C)),
% 5.63/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.63/5.85  thf('26', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 5.63/5.85      inference('demod', [status(thm)], ['24', '25'])).
% 5.63/5.85  thf('27', plain,
% 5.63/5.85      (![X2 : $i, X4 : $i]:
% 5.63/5.85         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 5.63/5.85      inference('cnf', [status(esa)], [d7_xboole_0])).
% 5.63/5.85  thf('28', plain,
% 5.63/5.85      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_A))),
% 5.63/5.85      inference('sup-', [status(thm)], ['26', '27'])).
% 5.63/5.85  thf('29', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 5.63/5.85      inference('simplify', [status(thm)], ['28'])).
% 5.63/5.85  thf(t78_xboole_1, axiom,
% 5.63/5.85    (![A:$i,B:$i,C:$i]:
% 5.63/5.85     ( ( r1_xboole_0 @ A @ B ) =>
% 5.63/5.85       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 5.63/5.85         ( k3_xboole_0 @ A @ C ) ) ))).
% 5.63/5.85  thf('30', plain,
% 5.63/5.85      (![X16 : $i, X17 : $i, X18 : $i]:
% 5.63/5.85         (~ (r1_xboole_0 @ X16 @ X17)
% 5.63/5.85          | ((k3_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 5.63/5.85              = (k3_xboole_0 @ X16 @ X18)))),
% 5.63/5.85      inference('cnf', [status(esa)], [t78_xboole_1])).
% 5.63/5.85  thf('31', plain,
% 5.63/5.85      (![X0 : $i]:
% 5.63/5.85         ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0))
% 5.63/5.85           = (k3_xboole_0 @ sk_B @ X0))),
% 5.63/5.85      inference('sup-', [status(thm)], ['29', '30'])).
% 5.63/5.85  thf('32', plain,
% 5.63/5.85      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.63/5.85      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.63/5.85  thf('33', plain,
% 5.63/5.85      (![X2 : $i, X4 : $i]:
% 5.63/5.85         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 5.63/5.85      inference('cnf', [status(esa)], [d7_xboole_0])).
% 5.63/5.85  thf('34', plain,
% 5.63/5.85      (![X0 : $i, X1 : $i]:
% 5.63/5.85         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 5.63/5.85      inference('sup-', [status(thm)], ['32', '33'])).
% 5.63/5.85  thf('35', plain,
% 5.63/5.85      (![X0 : $i]:
% 5.63/5.85         (((k3_xboole_0 @ sk_B @ X0) != (k1_xboole_0))
% 5.63/5.85          | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B))),
% 5.63/5.85      inference('sup-', [status(thm)], ['31', '34'])).
% 5.63/5.85  thf('36', plain,
% 5.63/5.85      ((((k1_xboole_0) != (k1_xboole_0))
% 5.63/5.85        | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_B))),
% 5.63/5.85      inference('sup-', [status(thm)], ['5', '35'])).
% 5.63/5.85  thf('37', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 5.63/5.85      inference('simplify', [status(thm)], ['36'])).
% 5.63/5.85  thf('38', plain, ($false), inference('demod', [status(thm)], ['0', '37'])).
% 5.63/5.85  
% 5.63/5.85  % SZS output end Refutation
% 5.63/5.85  
% 5.63/5.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
