%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IFsep6Y0V2

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:48 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   48 (  56 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  324 ( 407 expanded)
%              Number of equality atoms :   38 (  50 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X26 @ X26 @ X27 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X59: $i,X61: $i,X62: $i] :
      ( ( r1_tarski @ X61 @ ( k2_tarski @ X59 @ X62 ) )
      | ( X61
       != ( k1_tarski @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('2',plain,(
    ! [X59: $i,X62: $i] :
      ( r1_tarski @ ( k1_tarski @ X59 ) @ ( k2_tarski @ X59 @ X62 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('4',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B_1 ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('6',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) )
    = ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X26 @ X26 @ X27 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('8',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X26 @ X26 @ X27 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('9',plain,
    ( ( k3_xboole_0 @ ( k1_enumset1 @ sk_A @ sk_A @ sk_B_1 ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) )
    = ( k1_enumset1 @ sk_A @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_enumset1 @ sk_A @ sk_A @ sk_B_1 ) )
      | ( r1_tarski @ X0 @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(l29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
        = ( k1_tarski @ B ) )
     => ( r2_hidden @ B @ A ) ) )).

thf('18',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r2_hidden @ X53 @ X54 )
      | ( ( k3_xboole_0 @ X54 @ ( k1_tarski @ X53 ) )
       != ( k1_tarski @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[l29_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
       != ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['20'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('22',plain,(
    ! [X19: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X21 )
      | ( X23 = X22 )
      | ( X23 = X19 )
      | ( X21
       != ( k2_tarski @ X22 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('23',plain,(
    ! [X19: $i,X22: $i,X23: $i] :
      ( ( X23 = X19 )
      | ( X23 = X22 )
      | ~ ( r2_hidden @ X23 @ ( k2_tarski @ X22 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( sk_A = sk_C_1 )
    | ( sk_A = sk_D_1 ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['24','25','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IFsep6Y0V2
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:58:18 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 419 iterations in 0.203s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.65  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.45/0.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.65  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.65  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.45/0.65  thf(t70_enumset1, axiom,
% 0.45/0.65    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.45/0.65  thf('0', plain,
% 0.45/0.65      (![X26 : $i, X27 : $i]:
% 0.45/0.65         ((k1_enumset1 @ X26 @ X26 @ X27) = (k2_tarski @ X26 @ X27))),
% 0.45/0.65      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.65  thf(l45_zfmisc_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.45/0.65       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.45/0.65            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.45/0.65  thf('1', plain,
% 0.45/0.65      (![X59 : $i, X61 : $i, X62 : $i]:
% 0.45/0.65         ((r1_tarski @ X61 @ (k2_tarski @ X59 @ X62))
% 0.45/0.65          | ((X61) != (k1_tarski @ X59)))),
% 0.45/0.65      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.45/0.65  thf('2', plain,
% 0.45/0.65      (![X59 : $i, X62 : $i]:
% 0.45/0.65         (r1_tarski @ (k1_tarski @ X59) @ (k2_tarski @ X59 @ X62))),
% 0.45/0.65      inference('simplify', [status(thm)], ['1'])).
% 0.45/0.65  thf('3', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (r1_tarski @ (k1_tarski @ X1) @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['0', '2'])).
% 0.45/0.65  thf(t28_zfmisc_1, conjecture,
% 0.45/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.65     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.45/0.65          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.65    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.65        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.45/0.65             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.45/0.65    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.45/0.65  thf('4', plain,
% 0.45/0.65      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B_1) @ (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(t28_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.45/0.65  thf('5', plain,
% 0.45/0.65      (![X13 : $i, X14 : $i]:
% 0.45/0.65         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.45/0.65      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.45/0.65  thf('6', plain,
% 0.45/0.65      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ 
% 0.45/0.65         (k2_tarski @ sk_C_1 @ sk_D_1)) = (k2_tarski @ sk_A @ sk_B_1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.65  thf('7', plain,
% 0.45/0.65      (![X26 : $i, X27 : $i]:
% 0.45/0.65         ((k1_enumset1 @ X26 @ X26 @ X27) = (k2_tarski @ X26 @ X27))),
% 0.45/0.65      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.65  thf('8', plain,
% 0.45/0.65      (![X26 : $i, X27 : $i]:
% 0.45/0.65         ((k1_enumset1 @ X26 @ X26 @ X27) = (k2_tarski @ X26 @ X27))),
% 0.45/0.65      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.65  thf('9', plain,
% 0.45/0.65      (((k3_xboole_0 @ (k1_enumset1 @ sk_A @ sk_A @ sk_B_1) @ 
% 0.45/0.65         (k2_tarski @ sk_C_1 @ sk_D_1)) = (k1_enumset1 @ sk_A @ sk_A @ sk_B_1))),
% 0.45/0.65      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.45/0.65  thf(commutativity_k3_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.45/0.65  thf('10', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.65  thf(t18_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 0.45/0.65  thf('11', plain,
% 0.45/0.65      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.45/0.65         ((r1_tarski @ X10 @ X11)
% 0.45/0.65          | ~ (r1_tarski @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.45/0.65  thf('12', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.65  thf('13', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (r1_tarski @ X0 @ (k1_enumset1 @ sk_A @ sk_A @ sk_B_1))
% 0.45/0.65          | (r1_tarski @ X0 @ (k2_tarski @ sk_C_1 @ sk_D_1)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['9', '12'])).
% 0.45/0.65  thf('14', plain,
% 0.45/0.65      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['3', '13'])).
% 0.45/0.65  thf('15', plain,
% 0.45/0.65      (![X13 : $i, X14 : $i]:
% 0.45/0.65         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.45/0.65      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.45/0.65  thf('16', plain,
% 0.45/0.65      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D_1))
% 0.45/0.65         = (k1_tarski @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.65  thf('17', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.65  thf(l29_zfmisc_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 0.45/0.65       ( r2_hidden @ B @ A ) ))).
% 0.45/0.65  thf('18', plain,
% 0.45/0.65      (![X53 : $i, X54 : $i]:
% 0.45/0.65         ((r2_hidden @ X53 @ X54)
% 0.45/0.65          | ((k3_xboole_0 @ X54 @ (k1_tarski @ X53)) != (k1_tarski @ X53)))),
% 0.45/0.65      inference('cnf', [status(esa)], [l29_zfmisc_1])).
% 0.45/0.65  thf('19', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((k3_xboole_0 @ (k1_tarski @ X1) @ X0) != (k1_tarski @ X1))
% 0.45/0.65          | (r2_hidden @ X1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['17', '18'])).
% 0.45/0.65  thf('20', plain,
% 0.45/0.65      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.45/0.65        | (r2_hidden @ sk_A @ (k2_tarski @ sk_C_1 @ sk_D_1)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['16', '19'])).
% 0.45/0.65  thf('21', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.45/0.65      inference('simplify', [status(thm)], ['20'])).
% 0.45/0.65  thf(d2_tarski, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.45/0.65       ( ![D:$i]:
% 0.45/0.65         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.45/0.65  thf('22', plain,
% 0.45/0.65      (![X19 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X23 @ X21)
% 0.45/0.65          | ((X23) = (X22))
% 0.45/0.65          | ((X23) = (X19))
% 0.45/0.65          | ((X21) != (k2_tarski @ X22 @ X19)))),
% 0.45/0.65      inference('cnf', [status(esa)], [d2_tarski])).
% 0.45/0.65  thf('23', plain,
% 0.45/0.65      (![X19 : $i, X22 : $i, X23 : $i]:
% 0.45/0.65         (((X23) = (X19))
% 0.45/0.65          | ((X23) = (X22))
% 0.45/0.65          | ~ (r2_hidden @ X23 @ (k2_tarski @ X22 @ X19)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['22'])).
% 0.45/0.65  thf('24', plain, ((((sk_A) = (sk_C_1)) | ((sk_A) = (sk_D_1)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['21', '23'])).
% 0.45/0.65  thf('25', plain, (((sk_A) != (sk_D_1))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('26', plain, (((sk_A) != (sk_C_1))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('27', plain, ($false),
% 0.45/0.65      inference('simplify_reflect-', [status(thm)], ['24', '25', '26'])).
% 0.45/0.65  
% 0.45/0.65  % SZS output end Refutation
% 0.45/0.65  
% 0.45/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
