%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9VegIRHj8H

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:21 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   60 (  77 expanded)
%              Number of leaves         :   20 (  31 expanded)
%              Depth                    :   15
%              Number of atoms          :  398 ( 615 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C @ X13 @ X12 ) @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('1',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X31 ) @ X32 )
      | ( r2_hidden @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

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

thf('2',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('4',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('6',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D_1 ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k3_xboole_0 @ X12 @ X15 ) )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf('12',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_A )
    | ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('15',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_A )
    | ( r2_hidden @ sk_D_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('20',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('21',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_B )
    | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('25',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_B )
    | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('28',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    r2_hidden @ sk_D_1 @ sk_B ),
    inference(clc,[status(thm)],['25','28'])).

thf('30',plain,(
    r2_hidden @ sk_D_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('32',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_D_1 @ X0 )
      | ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k3_xboole_0 @ X12 @ X15 ) )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('36',plain,(
    ~ ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['36','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9VegIRHj8H
% 0.14/0.38  % Computer   : n005.cluster.edu
% 0.14/0.38  % Model      : x86_64 x86_64
% 0.14/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory     : 8042.1875MB
% 0.14/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 20:33:33 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.39  % Running in FO mode
% 0.45/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.63  % Solved by: fo/fo7.sh
% 0.45/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.63  % done 286 iterations in 0.144s
% 0.45/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.63  % SZS output start Refutation
% 0.45/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.63  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.45/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.63  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.63  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.45/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.63  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.63  thf(t4_xboole_0, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.63            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.63       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.45/0.63            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.45/0.63  thf('0', plain,
% 0.45/0.63      (![X12 : $i, X13 : $i]:
% 0.45/0.63         ((r1_xboole_0 @ X12 @ X13)
% 0.45/0.63          | (r2_hidden @ (sk_C @ X13 @ X12) @ (k3_xboole_0 @ X12 @ X13)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.45/0.63  thf(l27_zfmisc_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.45/0.63  thf('1', plain,
% 0.45/0.63      (![X31 : $i, X32 : $i]:
% 0.45/0.63         ((r1_xboole_0 @ (k1_tarski @ X31) @ X32) | (r2_hidden @ X31 @ X32))),
% 0.45/0.63      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.45/0.63  thf(t149_zfmisc_1, conjecture,
% 0.45/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.63     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.45/0.63         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.45/0.63       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.45/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.63    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.63        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.45/0.63            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.45/0.63          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 0.45/0.63    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 0.45/0.63  thf('2', plain,
% 0.45/0.63      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D_1))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(commutativity_k3_xboole_0, axiom,
% 0.45/0.63    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.45/0.63  thf('3', plain,
% 0.45/0.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.45/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.63  thf('4', plain,
% 0.45/0.63      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D_1))),
% 0.45/0.63      inference('demod', [status(thm)], ['2', '3'])).
% 0.45/0.63  thf(t28_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.45/0.63  thf('5', plain,
% 0.45/0.63      (![X16 : $i, X17 : $i]:
% 0.45/0.63         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.45/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.45/0.63  thf('6', plain,
% 0.45/0.63      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D_1))
% 0.45/0.63         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.63  thf('7', plain,
% 0.45/0.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.45/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.63  thf('8', plain,
% 0.45/0.63      (((k3_xboole_0 @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.45/0.63         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.45/0.63      inference('demod', [status(thm)], ['6', '7'])).
% 0.45/0.63  thf('9', plain,
% 0.45/0.63      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X14 @ (k3_xboole_0 @ X12 @ X15))
% 0.45/0.63          | ~ (r1_xboole_0 @ X12 @ X15))),
% 0.45/0.63      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.45/0.63  thf('10', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.45/0.63          | ~ (r1_xboole_0 @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.63  thf('11', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((r2_hidden @ sk_D_1 @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.45/0.63          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['1', '10'])).
% 0.45/0.63  thf('12', plain,
% 0.45/0.63      (((r1_xboole_0 @ sk_B @ sk_A)
% 0.45/0.63        | (r2_hidden @ sk_D_1 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['0', '11'])).
% 0.45/0.63  thf('13', plain,
% 0.45/0.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.45/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.63  thf(d4_xboole_0, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.45/0.63       ( ![D:$i]:
% 0.45/0.63         ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.63           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.45/0.63  thf('14', plain,
% 0.45/0.63      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X8 @ X7)
% 0.45/0.63          | (r2_hidden @ X8 @ X6)
% 0.45/0.63          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 0.45/0.63      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.45/0.63  thf('15', plain,
% 0.45/0.63      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.45/0.63         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.45/0.63      inference('simplify', [status(thm)], ['14'])).
% 0.45/0.63  thf('16', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['13', '15'])).
% 0.45/0.63  thf('17', plain,
% 0.45/0.63      (((r1_xboole_0 @ sk_B @ sk_A) | (r2_hidden @ sk_D_1 @ sk_B))),
% 0.45/0.63      inference('sup-', [status(thm)], ['12', '16'])).
% 0.45/0.63  thf('18', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(symmetry_r1_xboole_0, axiom,
% 0.45/0.63    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.45/0.63  thf('19', plain,
% 0.45/0.63      (![X10 : $i, X11 : $i]:
% 0.45/0.63         ((r1_xboole_0 @ X10 @ X11) | ~ (r1_xboole_0 @ X11 @ X10))),
% 0.45/0.63      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.45/0.63  thf('20', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.45/0.63      inference('sup-', [status(thm)], ['18', '19'])).
% 0.45/0.63  thf(t70_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.45/0.63            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.45/0.63       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.45/0.63            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.45/0.63  thf('21', plain,
% 0.45/0.63      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.63         ((r1_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 0.45/0.63          | ~ (r1_xboole_0 @ X18 @ X19)
% 0.45/0.63          | ~ (r1_xboole_0 @ X18 @ X20))),
% 0.45/0.63      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.45/0.63  thf('22', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (r1_xboole_0 @ sk_B @ X0)
% 0.45/0.63          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ X0)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.63  thf('23', plain,
% 0.45/0.63      (((r2_hidden @ sk_D_1 @ sk_B)
% 0.45/0.63        | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['17', '22'])).
% 0.45/0.63  thf('24', plain,
% 0.45/0.63      (![X10 : $i, X11 : $i]:
% 0.45/0.63         ((r1_xboole_0 @ X10 @ X11) | ~ (r1_xboole_0 @ X11 @ X10))),
% 0.45/0.63      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.45/0.63  thf('25', plain,
% 0.45/0.63      (((r2_hidden @ sk_D_1 @ sk_B)
% 0.45/0.63        | (r1_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_B))),
% 0.45/0.63      inference('sup-', [status(thm)], ['23', '24'])).
% 0.45/0.63  thf('26', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(commutativity_k2_xboole_0, axiom,
% 0.45/0.63    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.45/0.63  thf('27', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.45/0.63  thf('28', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_B)),
% 0.45/0.63      inference('demod', [status(thm)], ['26', '27'])).
% 0.45/0.63  thf('29', plain, ((r2_hidden @ sk_D_1 @ sk_B)),
% 0.45/0.63      inference('clc', [status(thm)], ['25', '28'])).
% 0.45/0.63  thf('30', plain, ((r2_hidden @ sk_D_1 @ sk_C_1)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('31', plain,
% 0.45/0.63      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X4 @ X5)
% 0.45/0.63          | ~ (r2_hidden @ X4 @ X6)
% 0.45/0.63          | (r2_hidden @ X4 @ X7)
% 0.45/0.63          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 0.45/0.63      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.45/0.63  thf('32', plain,
% 0.45/0.63      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.63         ((r2_hidden @ X4 @ (k3_xboole_0 @ X5 @ X6))
% 0.45/0.63          | ~ (r2_hidden @ X4 @ X6)
% 0.45/0.63          | ~ (r2_hidden @ X4 @ X5))),
% 0.45/0.63      inference('simplify', [status(thm)], ['31'])).
% 0.45/0.63  thf('33', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (r2_hidden @ sk_D_1 @ X0)
% 0.45/0.63          | (r2_hidden @ sk_D_1 @ (k3_xboole_0 @ X0 @ sk_C_1)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['30', '32'])).
% 0.45/0.63  thf('34', plain, ((r2_hidden @ sk_D_1 @ (k3_xboole_0 @ sk_B @ sk_C_1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['29', '33'])).
% 0.45/0.63  thf('35', plain,
% 0.45/0.63      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X14 @ (k3_xboole_0 @ X12 @ X15))
% 0.45/0.63          | ~ (r1_xboole_0 @ X12 @ X15))),
% 0.45/0.63      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.45/0.63  thf('36', plain, (~ (r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.45/0.63      inference('sup-', [status(thm)], ['34', '35'])).
% 0.45/0.63  thf('37', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.45/0.63      inference('sup-', [status(thm)], ['18', '19'])).
% 0.45/0.63  thf('38', plain, ($false), inference('demod', [status(thm)], ['36', '37'])).
% 0.45/0.63  
% 0.45/0.63  % SZS output end Refutation
% 0.45/0.63  
% 0.47/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
