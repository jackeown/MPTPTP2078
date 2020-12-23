%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pBVOzheJ7g

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:25 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   55 (  67 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :   14
%              Number of atoms          :  360 ( 532 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

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
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_B @ sk_C_2 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X14 @ X15 )
      | ( r2_hidden @ ( sk_C_1 @ X15 @ X14 ) @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('5',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X30 ) @ X31 )
      | ( r2_hidden @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('6',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D_1 ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k3_xboole_0 @ X14 @ X17 ) )
      | ~ ( r1_xboole_0 @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','14'])).

thf('16',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_A )
    | ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('19',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_A )
    | ( r2_hidden @ sk_D_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r2_hidden @ sk_D_1 @ sk_C_2 ),
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

thf('24',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_2 @ X0 )
      | ~ ( r2_hidden @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( r2_hidden @ sk_D_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['21','26'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('28',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) )
      | ~ ( r1_xboole_0 @ X20 @ X21 )
      | ~ ( r1_xboole_0 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['3','29'])).

thf('31',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('32',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['0','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pBVOzheJ7g
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:40:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.59/0.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.83  % Solved by: fo/fo7.sh
% 0.59/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.83  % done 905 iterations in 0.375s
% 0.59/0.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.83  % SZS output start Refutation
% 0.59/0.83  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.59/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.83  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.83  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.59/0.83  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.83  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.83  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.59/0.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.83  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.59/0.83  thf(t149_zfmisc_1, conjecture,
% 0.59/0.83    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.83     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.59/0.83         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.59/0.83       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.59/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.83    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.83        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.59/0.83            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.59/0.83          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 0.59/0.83    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 0.59/0.83  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('1', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf(symmetry_r1_xboole_0, axiom,
% 0.59/0.83    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.59/0.83  thf('2', plain,
% 0.59/0.83      (![X8 : $i, X9 : $i]:
% 0.59/0.83         ((r1_xboole_0 @ X8 @ X9) | ~ (r1_xboole_0 @ X9 @ X8))),
% 0.59/0.83      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.59/0.83  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C_2)),
% 0.59/0.83      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.83  thf(t4_xboole_0, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.59/0.83            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.59/0.83       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.59/0.83            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.59/0.83  thf('4', plain,
% 0.59/0.83      (![X14 : $i, X15 : $i]:
% 0.59/0.83         ((r1_xboole_0 @ X14 @ X15)
% 0.59/0.83          | (r2_hidden @ (sk_C_1 @ X15 @ X14) @ (k3_xboole_0 @ X14 @ X15)))),
% 0.59/0.83      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.59/0.83  thf(l27_zfmisc_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.59/0.83  thf('5', plain,
% 0.59/0.83      (![X30 : $i, X31 : $i]:
% 0.59/0.83         ((r1_xboole_0 @ (k1_tarski @ X30) @ X31) | (r2_hidden @ X30 @ X31))),
% 0.59/0.83      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.59/0.83  thf('6', plain,
% 0.59/0.83      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D_1))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf(commutativity_k3_xboole_0, axiom,
% 0.59/0.83    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.59/0.83  thf('7', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.83  thf('8', plain,
% 0.59/0.83      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D_1))),
% 0.59/0.83      inference('demod', [status(thm)], ['6', '7'])).
% 0.59/0.83  thf(t28_xboole_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.59/0.83  thf('9', plain,
% 0.59/0.83      (![X18 : $i, X19 : $i]:
% 0.59/0.83         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 0.59/0.83      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.83  thf('10', plain,
% 0.59/0.83      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D_1))
% 0.59/0.83         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.59/0.83      inference('sup-', [status(thm)], ['8', '9'])).
% 0.59/0.83  thf('11', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.83  thf('12', plain,
% 0.59/0.83      (((k3_xboole_0 @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.59/0.83         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.59/0.83      inference('demod', [status(thm)], ['10', '11'])).
% 0.59/0.83  thf('13', plain,
% 0.59/0.83      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.59/0.83         (~ (r2_hidden @ X16 @ (k3_xboole_0 @ X14 @ X17))
% 0.59/0.83          | ~ (r1_xboole_0 @ X14 @ X17))),
% 0.59/0.83      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.59/0.83  thf('14', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.59/0.83          | ~ (r1_xboole_0 @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['12', '13'])).
% 0.59/0.83  thf('15', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((r2_hidden @ sk_D_1 @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.59/0.83          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['5', '14'])).
% 0.59/0.83  thf('16', plain,
% 0.59/0.83      (((r1_xboole_0 @ sk_B @ sk_A)
% 0.59/0.83        | (r2_hidden @ sk_D_1 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['4', '15'])).
% 0.59/0.83  thf('17', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.83  thf(d4_xboole_0, axiom,
% 0.59/0.83    (![A:$i,B:$i,C:$i]:
% 0.59/0.83     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.59/0.83       ( ![D:$i]:
% 0.59/0.83         ( ( r2_hidden @ D @ C ) <=>
% 0.59/0.83           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.59/0.83  thf('18', plain,
% 0.59/0.83      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.59/0.83         (~ (r2_hidden @ X6 @ X5)
% 0.59/0.83          | (r2_hidden @ X6 @ X4)
% 0.59/0.83          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.59/0.83      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.59/0.83  thf('19', plain,
% 0.59/0.83      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.59/0.83         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.59/0.83      inference('simplify', [status(thm)], ['18'])).
% 0.59/0.83  thf('20', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.83         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.59/0.83      inference('sup-', [status(thm)], ['17', '19'])).
% 0.59/0.83  thf('21', plain,
% 0.59/0.83      (((r1_xboole_0 @ sk_B @ sk_A) | (r2_hidden @ sk_D_1 @ sk_B))),
% 0.59/0.83      inference('sup-', [status(thm)], ['16', '20'])).
% 0.59/0.83  thf('22', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('23', plain, ((r2_hidden @ sk_D_1 @ sk_C_2)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf(t3_xboole_0, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.59/0.83            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.59/0.83       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.59/0.83            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.59/0.83  thf('24', plain,
% 0.59/0.83      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.59/0.83         (~ (r2_hidden @ X12 @ X10)
% 0.59/0.83          | ~ (r2_hidden @ X12 @ X13)
% 0.59/0.83          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.59/0.83      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.59/0.83  thf('25', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (r1_xboole_0 @ sk_C_2 @ X0) | ~ (r2_hidden @ sk_D_1 @ X0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['23', '24'])).
% 0.59/0.83  thf('26', plain, (~ (r2_hidden @ sk_D_1 @ sk_B)),
% 0.59/0.83      inference('sup-', [status(thm)], ['22', '25'])).
% 0.59/0.83  thf('27', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.59/0.83      inference('clc', [status(thm)], ['21', '26'])).
% 0.59/0.83  thf(t70_xboole_1, axiom,
% 0.59/0.83    (![A:$i,B:$i,C:$i]:
% 0.59/0.83     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.59/0.83            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.59/0.83       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.59/0.83            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.59/0.83  thf('28', plain,
% 0.59/0.83      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.59/0.83         ((r1_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X22))
% 0.59/0.83          | ~ (r1_xboole_0 @ X20 @ X21)
% 0.59/0.83          | ~ (r1_xboole_0 @ X20 @ X22))),
% 0.59/0.83      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.59/0.83  thf('29', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (r1_xboole_0 @ sk_B @ X0)
% 0.59/0.83          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['27', '28'])).
% 0.59/0.83  thf('30', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_2))),
% 0.59/0.83      inference('sup-', [status(thm)], ['3', '29'])).
% 0.59/0.83  thf('31', plain,
% 0.59/0.83      (![X8 : $i, X9 : $i]:
% 0.59/0.83         ((r1_xboole_0 @ X8 @ X9) | ~ (r1_xboole_0 @ X9 @ X8))),
% 0.59/0.83      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.59/0.83  thf('32', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 0.59/0.83      inference('sup-', [status(thm)], ['30', '31'])).
% 0.59/0.83  thf('33', plain, ($false), inference('demod', [status(thm)], ['0', '32'])).
% 0.59/0.83  
% 0.59/0.83  % SZS output end Refutation
% 0.59/0.83  
% 0.59/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
