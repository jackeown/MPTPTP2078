%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qmkBLqpJ17

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:50 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   67 (  85 expanded)
%              Number of leaves         :   22 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  407 ( 569 expanded)
%              Number of equality atoms :   27 (  43 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t45_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
     => ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
       => ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t45_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
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

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('2',plain,(
    ! [X32: $i,X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X35 @ X34 )
      | ( X35 = X32 )
      | ( X34
       != ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('3',plain,(
    ! [X32: $i,X35: $i] :
      ( ( X35 = X32 )
      | ~ ( r2_hidden @ X35 @ ( k1_tarski @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('9',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_tarski @ X31 @ X30 )
      = ( k2_tarski @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X47 @ X48 ) )
      = ( k2_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X47 @ X48 ) )
      = ( k2_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ sk_B_1 ),
    inference(demod,[status(thm)],['8','13'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X17: $i,X19: $i] :
      ( ( X17 = X19 )
      | ~ ( r1_tarski @ X19 @ X17 )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
    | ( sk_B_1
      = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X28: $i,X29: $i] :
      ( r1_tarski @ X28 @ ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('19',plain,(
    ! [X22: $i,X23: $i,X25: $i] :
      ( ( r1_xboole_0 @ X22 @ X25 )
      | ~ ( r1_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_B_1 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','20'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('22',plain,(
    ! [X37: $i] :
      ( ( k2_tarski @ X37 @ X37 )
      = ( k1_tarski @ X37 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('23',plain,(
    ! [X37: $i] :
      ( ( k2_tarski @ X37 @ X37 )
      = ( k1_tarski @ X37 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('24',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('25',plain,(
    ! [X32: $i,X35: $i] :
      ( ( X35 = X32 )
      | ~ ( r2_hidden @ X35 @ ( k1_tarski @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ ( k2_tarski @ X0 @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X33 != X32 )
      | ( r2_hidden @ X33 @ X34 )
      | ( X34
       != ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('29',plain,(
    ! [X32: $i] :
      ( r2_hidden @ X32 @ ( k1_tarski @ X32 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference(clc,[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['22','32'])).

thf('34',plain,(
    ! [X32: $i] :
      ( r2_hidden @ X32 @ ( k1_tarski @ X32 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('35',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('36',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X13 )
      | ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('41',plain,(
    ! [X0: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference('sup-',[status(thm)],['21','41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['0','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qmkBLqpJ17
% 0.12/0.32  % Computer   : n005.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 10:41:48 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running portfolio for 600 s
% 0.12/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.39/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.59  % Solved by: fo/fo7.sh
% 0.39/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.59  % done 324 iterations in 0.152s
% 0.39/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.59  % SZS output start Refutation
% 0.39/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.39/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.39/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.59  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.39/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.59  thf(t45_zfmisc_1, conjecture,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.39/0.59       ( r2_hidden @ A @ B ) ))).
% 0.39/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.59    (~( ![A:$i,B:$i]:
% 0.39/0.59        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.39/0.59          ( r2_hidden @ A @ B ) ) )),
% 0.39/0.59    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 0.39/0.59  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B_1)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(t3_xboole_0, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.39/0.59            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.39/0.59       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.39/0.59            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.39/0.59  thf('1', plain,
% 0.39/0.59      (![X13 : $i, X14 : $i]:
% 0.39/0.59         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X13))),
% 0.39/0.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.39/0.59  thf(d1_tarski, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.39/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.39/0.59  thf('2', plain,
% 0.39/0.59      (![X32 : $i, X34 : $i, X35 : $i]:
% 0.39/0.59         (~ (r2_hidden @ X35 @ X34)
% 0.39/0.59          | ((X35) = (X32))
% 0.39/0.59          | ((X34) != (k1_tarski @ X32)))),
% 0.39/0.59      inference('cnf', [status(esa)], [d1_tarski])).
% 0.39/0.59  thf('3', plain,
% 0.39/0.59      (![X32 : $i, X35 : $i]:
% 0.39/0.59         (((X35) = (X32)) | ~ (r2_hidden @ X35 @ (k1_tarski @ X32)))),
% 0.39/0.59      inference('simplify', [status(thm)], ['2'])).
% 0.39/0.59  thf('4', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.39/0.59          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['1', '3'])).
% 0.39/0.59  thf('5', plain,
% 0.39/0.59      (![X13 : $i, X14 : $i]:
% 0.39/0.59         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X14))),
% 0.39/0.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.39/0.59  thf('6', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((r2_hidden @ X0 @ X1)
% 0.39/0.59          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.39/0.59          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.39/0.59      inference('sup+', [status(thm)], ['4', '5'])).
% 0.39/0.59  thf('7', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.39/0.59      inference('simplify', [status(thm)], ['6'])).
% 0.39/0.59  thf('8', plain,
% 0.39/0.59      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) @ sk_B_1)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(commutativity_k2_tarski, axiom,
% 0.39/0.59    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.39/0.59  thf('9', plain,
% 0.39/0.59      (![X30 : $i, X31 : $i]:
% 0.39/0.59         ((k2_tarski @ X31 @ X30) = (k2_tarski @ X30 @ X31))),
% 0.39/0.59      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.39/0.59  thf(l51_zfmisc_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.59  thf('10', plain,
% 0.39/0.59      (![X47 : $i, X48 : $i]:
% 0.39/0.59         ((k3_tarski @ (k2_tarski @ X47 @ X48)) = (k2_xboole_0 @ X47 @ X48))),
% 0.39/0.59      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.39/0.59  thf('11', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.59      inference('sup+', [status(thm)], ['9', '10'])).
% 0.39/0.59  thf('12', plain,
% 0.39/0.59      (![X47 : $i, X48 : $i]:
% 0.39/0.59         ((k3_tarski @ (k2_tarski @ X47 @ X48)) = (k2_xboole_0 @ X47 @ X48))),
% 0.39/0.59      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.39/0.59  thf('13', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.59      inference('sup+', [status(thm)], ['11', '12'])).
% 0.39/0.59  thf('14', plain,
% 0.39/0.59      ((r1_tarski @ (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ sk_B_1)),
% 0.39/0.59      inference('demod', [status(thm)], ['8', '13'])).
% 0.39/0.59  thf(d10_xboole_0, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.59  thf('15', plain,
% 0.39/0.59      (![X17 : $i, X19 : $i]:
% 0.39/0.59         (((X17) = (X19))
% 0.39/0.59          | ~ (r1_tarski @ X19 @ X17)
% 0.39/0.59          | ~ (r1_tarski @ X17 @ X19))),
% 0.39/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.59  thf('16', plain,
% 0.39/0.59      ((~ (r1_tarski @ sk_B_1 @ (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))
% 0.39/0.59        | ((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['14', '15'])).
% 0.39/0.59  thf(t7_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.59  thf('17', plain,
% 0.39/0.59      (![X28 : $i, X29 : $i]: (r1_tarski @ X28 @ (k2_xboole_0 @ X28 @ X29))),
% 0.39/0.59      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.39/0.59  thf('18', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.39/0.59      inference('demod', [status(thm)], ['16', '17'])).
% 0.39/0.59  thf(t70_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.39/0.59            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.39/0.59       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.39/0.59            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.39/0.59  thf('19', plain,
% 0.39/0.59      (![X22 : $i, X23 : $i, X25 : $i]:
% 0.39/0.59         ((r1_xboole_0 @ X22 @ X25)
% 0.39/0.59          | ~ (r1_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X25)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.39/0.59  thf('20', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (r1_xboole_0 @ X0 @ sk_B_1)
% 0.39/0.59          | (r1_xboole_0 @ X0 @ (k1_tarski @ sk_A)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.59  thf('21', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((r2_hidden @ X0 @ sk_B_1)
% 0.39/0.59          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ sk_A)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['7', '20'])).
% 0.39/0.59  thf(t69_enumset1, axiom,
% 0.39/0.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.39/0.59  thf('22', plain,
% 0.39/0.59      (![X37 : $i]: ((k2_tarski @ X37 @ X37) = (k1_tarski @ X37))),
% 0.39/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.59  thf('23', plain,
% 0.39/0.59      (![X37 : $i]: ((k2_tarski @ X37 @ X37) = (k1_tarski @ X37))),
% 0.39/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.59  thf(d1_xboole_0, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.39/0.59  thf('24', plain,
% 0.39/0.59      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.39/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.59  thf('25', plain,
% 0.39/0.59      (![X32 : $i, X35 : $i]:
% 0.39/0.59         (((X35) = (X32)) | ~ (r2_hidden @ X35 @ (k1_tarski @ X32)))),
% 0.39/0.59      inference('simplify', [status(thm)], ['2'])).
% 0.39/0.59  thf('26', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((v1_xboole_0 @ (k1_tarski @ X0)) | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.59  thf('27', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (((sk_B @ (k2_tarski @ X0 @ X0)) = (X0))
% 0.39/0.59          | (v1_xboole_0 @ (k1_tarski @ X0)))),
% 0.39/0.59      inference('sup+', [status(thm)], ['23', '26'])).
% 0.39/0.59  thf('28', plain,
% 0.39/0.59      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.39/0.59         (((X33) != (X32))
% 0.39/0.59          | (r2_hidden @ X33 @ X34)
% 0.39/0.59          | ((X34) != (k1_tarski @ X32)))),
% 0.39/0.59      inference('cnf', [status(esa)], [d1_tarski])).
% 0.39/0.59  thf('29', plain, (![X32 : $i]: (r2_hidden @ X32 @ (k1_tarski @ X32))),
% 0.39/0.59      inference('simplify', [status(thm)], ['28'])).
% 0.39/0.59  thf('30', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.59  thf('31', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['29', '30'])).
% 0.39/0.59  thf('32', plain, (![X0 : $i]: ((sk_B @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.39/0.59      inference('clc', [status(thm)], ['27', '31'])).
% 0.39/0.59  thf('33', plain, (![X0 : $i]: ((sk_B @ (k1_tarski @ X0)) = (X0))),
% 0.39/0.59      inference('sup+', [status(thm)], ['22', '32'])).
% 0.39/0.59  thf('34', plain, (![X32 : $i]: (r2_hidden @ X32 @ (k1_tarski @ X32))),
% 0.39/0.59      inference('simplify', [status(thm)], ['28'])).
% 0.39/0.59  thf('35', plain,
% 0.39/0.59      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.39/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.59  thf('36', plain,
% 0.39/0.59      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.39/0.59         (~ (r2_hidden @ X15 @ X13)
% 0.39/0.59          | ~ (r2_hidden @ X15 @ X16)
% 0.39/0.59          | ~ (r1_xboole_0 @ X13 @ X16))),
% 0.39/0.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.39/0.59  thf('37', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((v1_xboole_0 @ X0)
% 0.39/0.59          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.39/0.59          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.39/0.59      inference('sup-', [status(thm)], ['35', '36'])).
% 0.39/0.59  thf('38', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (r1_xboole_0 @ X0 @ (k1_tarski @ (sk_B @ X0))) | (v1_xboole_0 @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['34', '37'])).
% 0.39/0.59  thf('39', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.39/0.59          | (v1_xboole_0 @ (k1_tarski @ X0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['33', '38'])).
% 0.39/0.59  thf('40', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['29', '30'])).
% 0.39/0.59  thf('41', plain,
% 0.39/0.59      (![X0 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.39/0.59      inference('clc', [status(thm)], ['39', '40'])).
% 0.39/0.59  thf('42', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.39/0.59      inference('sup-', [status(thm)], ['21', '41'])).
% 0.39/0.59  thf('43', plain, ($false), inference('demod', [status(thm)], ['0', '42'])).
% 0.39/0.59  
% 0.39/0.59  % SZS output end Refutation
% 0.39/0.59  
% 0.39/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
