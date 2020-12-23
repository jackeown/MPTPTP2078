%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Vb0MWbujFd

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:47 EST 2020

% Result     : Theorem 0.85s
% Output     : Refutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :   70 (  82 expanded)
%              Number of leaves         :   30 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :  450 ( 540 expanded)
%              Number of equality atoms :   31 (  39 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('1',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('2',plain,(
    ! [X45: $i,X46: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X45 ) @ X46 )
      | ( r2_hidden @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t45_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
     => ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
       => ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t45_zfmisc_1])).

thf('3',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
    | ( sk_B_1
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('6',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_tarski @ X26 @ X25 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X47 @ X48 ) )
      = ( k2_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X47 @ X48 ) )
      = ( k2_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('13',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','10','11','12'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ( r1_xboole_0 @ X16 @ X19 )
      | ~ ( r1_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_B_1 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','15'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('17',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k4_xboole_0 @ X22 @ X23 )
        = X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_A ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ~ ( r2_hidden @ X9 @ X7 )
      | ( X8
       != ( k4_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('20',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ ( k4_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B_1 )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','22'])).

thf('24',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_xboole_0 @ ( k1_tarski @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('27',plain,(
    ! [X39: $i] :
      ( ( k2_tarski @ X39 @ X39 )
      = ( k1_tarski @ X39 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_enumset1 @ X40 @ X40 @ X41 )
      = ( k2_tarski @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 )
      | ( r2_hidden @ X32 @ X36 )
      | ( X36
       != ( k1_enumset1 @ X35 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('30',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( r2_hidden @ X32 @ ( k1_enumset1 @ X35 @ X34 @ X33 ) )
      | ( zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( X28 != X27 )
      | ~ ( zip_tseitin_0 @ X28 @ X29 @ X30 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('33',plain,(
    ! [X27: $i,X29: $i,X30: $i] :
      ~ ( zip_tseitin_0 @ X27 @ X29 @ X30 @ X27 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','36'])).

thf('38',plain,(
    $false ),
    inference('sup-',[status(thm)],['26','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Vb0MWbujFd
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:43:17 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.85/1.03  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.85/1.03  % Solved by: fo/fo7.sh
% 0.85/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.85/1.03  % done 699 iterations in 0.584s
% 0.85/1.03  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.85/1.03  % SZS output start Refutation
% 0.85/1.03  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.85/1.03  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.85/1.03  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.85/1.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.85/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.85/1.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.85/1.03  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.85/1.03  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.85/1.03  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.85/1.03  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.85/1.03  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.85/1.03  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.85/1.03  thf(sk_B_type, type, sk_B: $i > $i).
% 0.85/1.03  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.85/1.03  thf(d1_xboole_0, axiom,
% 0.85/1.03    (![A:$i]:
% 0.85/1.03     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.85/1.03  thf('0', plain,
% 0.85/1.03      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.85/1.03      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.85/1.03  thf('1', plain,
% 0.85/1.03      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.85/1.03      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.85/1.03  thf(l27_zfmisc_1, axiom,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.85/1.03  thf('2', plain,
% 0.85/1.03      (![X45 : $i, X46 : $i]:
% 0.85/1.03         ((r1_xboole_0 @ (k1_tarski @ X45) @ X46) | (r2_hidden @ X45 @ X46))),
% 0.85/1.03      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.85/1.03  thf(t45_zfmisc_1, conjecture,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.85/1.03       ( r2_hidden @ A @ B ) ))).
% 0.85/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.85/1.03    (~( ![A:$i,B:$i]:
% 0.85/1.03        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.85/1.03          ( r2_hidden @ A @ B ) ) )),
% 0.85/1.03    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 0.85/1.03  thf('3', plain,
% 0.85/1.03      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) @ sk_B_1)),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf(d10_xboole_0, axiom,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.85/1.03  thf('4', plain,
% 0.85/1.03      (![X11 : $i, X13 : $i]:
% 0.85/1.03         (((X11) = (X13))
% 0.85/1.03          | ~ (r1_tarski @ X13 @ X11)
% 0.85/1.03          | ~ (r1_tarski @ X11 @ X13))),
% 0.85/1.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.85/1.03  thf('5', plain,
% 0.85/1.03      ((~ (r1_tarski @ sk_B_1 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.85/1.03        | ((sk_B_1) = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['3', '4'])).
% 0.85/1.03  thf(commutativity_k2_tarski, axiom,
% 0.85/1.03    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.85/1.03  thf('6', plain,
% 0.85/1.03      (![X25 : $i, X26 : $i]:
% 0.85/1.03         ((k2_tarski @ X26 @ X25) = (k2_tarski @ X25 @ X26))),
% 0.85/1.03      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.85/1.03  thf(l51_zfmisc_1, axiom,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.85/1.03  thf('7', plain,
% 0.85/1.03      (![X47 : $i, X48 : $i]:
% 0.85/1.03         ((k3_tarski @ (k2_tarski @ X47 @ X48)) = (k2_xboole_0 @ X47 @ X48))),
% 0.85/1.03      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.85/1.03  thf('8', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.85/1.03      inference('sup+', [status(thm)], ['6', '7'])).
% 0.85/1.03  thf('9', plain,
% 0.85/1.03      (![X47 : $i, X48 : $i]:
% 0.85/1.03         ((k3_tarski @ (k2_tarski @ X47 @ X48)) = (k2_xboole_0 @ X47 @ X48))),
% 0.85/1.03      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.85/1.03  thf('10', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.85/1.03      inference('sup+', [status(thm)], ['8', '9'])).
% 0.85/1.03  thf(t7_xboole_1, axiom,
% 0.85/1.03    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.85/1.03  thf('11', plain,
% 0.85/1.03      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 0.85/1.03      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.85/1.03  thf('12', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.85/1.03      inference('sup+', [status(thm)], ['8', '9'])).
% 0.85/1.03  thf('13', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.85/1.03      inference('demod', [status(thm)], ['5', '10', '11', '12'])).
% 0.85/1.03  thf(t70_xboole_1, axiom,
% 0.85/1.03    (![A:$i,B:$i,C:$i]:
% 0.85/1.03     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.85/1.03            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.85/1.03       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.85/1.03            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.85/1.03  thf('14', plain,
% 0.85/1.03      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.85/1.03         ((r1_xboole_0 @ X16 @ X19)
% 0.85/1.03          | ~ (r1_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X19)))),
% 0.85/1.03      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.85/1.03  thf('15', plain,
% 0.85/1.03      (![X0 : $i]:
% 0.85/1.03         (~ (r1_xboole_0 @ X0 @ sk_B_1)
% 0.85/1.03          | (r1_xboole_0 @ X0 @ (k1_tarski @ sk_A)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['13', '14'])).
% 0.85/1.03  thf('16', plain,
% 0.85/1.03      (![X0 : $i]:
% 0.85/1.03         ((r2_hidden @ X0 @ sk_B_1)
% 0.85/1.03          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ sk_A)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['2', '15'])).
% 0.85/1.03  thf(t83_xboole_1, axiom,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.85/1.03  thf('17', plain,
% 0.85/1.03      (![X22 : $i, X23 : $i]:
% 0.85/1.03         (((k4_xboole_0 @ X22 @ X23) = (X22)) | ~ (r1_xboole_0 @ X22 @ X23))),
% 0.85/1.03      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.85/1.03  thf('18', plain,
% 0.85/1.03      (![X0 : $i]:
% 0.85/1.03         ((r2_hidden @ X0 @ sk_B_1)
% 0.85/1.03          | ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ sk_A))
% 0.85/1.03              = (k1_tarski @ X0)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['16', '17'])).
% 0.85/1.03  thf(d5_xboole_0, axiom,
% 0.85/1.03    (![A:$i,B:$i,C:$i]:
% 0.85/1.03     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.85/1.03       ( ![D:$i]:
% 0.85/1.03         ( ( r2_hidden @ D @ C ) <=>
% 0.85/1.03           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.85/1.03  thf('19', plain,
% 0.85/1.03      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.85/1.03         (~ (r2_hidden @ X9 @ X8)
% 0.85/1.03          | ~ (r2_hidden @ X9 @ X7)
% 0.85/1.03          | ((X8) != (k4_xboole_0 @ X6 @ X7)))),
% 0.85/1.03      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.85/1.03  thf('20', plain,
% 0.85/1.03      (![X6 : $i, X7 : $i, X9 : $i]:
% 0.85/1.03         (~ (r2_hidden @ X9 @ X7)
% 0.85/1.03          | ~ (r2_hidden @ X9 @ (k4_xboole_0 @ X6 @ X7)))),
% 0.85/1.03      inference('simplify', [status(thm)], ['19'])).
% 0.85/1.03  thf('21', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.85/1.03          | (r2_hidden @ X0 @ sk_B_1)
% 0.85/1.03          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_A)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['18', '20'])).
% 0.85/1.03  thf('22', plain,
% 0.85/1.03      (![X0 : $i]:
% 0.85/1.03         ((v1_xboole_0 @ (k1_tarski @ sk_A))
% 0.85/1.03          | (r2_hidden @ X0 @ sk_B_1)
% 0.85/1.03          | ~ (r2_hidden @ (sk_B @ (k1_tarski @ sk_A)) @ (k1_tarski @ X0)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['1', '21'])).
% 0.85/1.03  thf('23', plain,
% 0.85/1.03      (((v1_xboole_0 @ (k1_tarski @ sk_A))
% 0.85/1.03        | (r2_hidden @ sk_A @ sk_B_1)
% 0.85/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_A)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['0', '22'])).
% 0.85/1.03  thf('24', plain,
% 0.85/1.03      (((r2_hidden @ sk_A @ sk_B_1) | (v1_xboole_0 @ (k1_tarski @ sk_A)))),
% 0.85/1.03      inference('simplify', [status(thm)], ['23'])).
% 0.85/1.03  thf('25', plain, (~ (r2_hidden @ sk_A @ sk_B_1)),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('26', plain, ((v1_xboole_0 @ (k1_tarski @ sk_A))),
% 0.85/1.03      inference('clc', [status(thm)], ['24', '25'])).
% 0.85/1.03  thf(t69_enumset1, axiom,
% 0.85/1.03    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.85/1.03  thf('27', plain,
% 0.85/1.03      (![X39 : $i]: ((k2_tarski @ X39 @ X39) = (k1_tarski @ X39))),
% 0.85/1.03      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.85/1.03  thf(t70_enumset1, axiom,
% 0.85/1.03    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.85/1.03  thf('28', plain,
% 0.85/1.03      (![X40 : $i, X41 : $i]:
% 0.85/1.03         ((k1_enumset1 @ X40 @ X40 @ X41) = (k2_tarski @ X40 @ X41))),
% 0.85/1.03      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.85/1.03  thf(d1_enumset1, axiom,
% 0.85/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.85/1.03     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.85/1.03       ( ![E:$i]:
% 0.85/1.03         ( ( r2_hidden @ E @ D ) <=>
% 0.85/1.03           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.85/1.03  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.85/1.03  thf(zf_stmt_2, axiom,
% 0.85/1.03    (![E:$i,C:$i,B:$i,A:$i]:
% 0.85/1.03     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.85/1.03       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.85/1.03  thf(zf_stmt_3, axiom,
% 0.85/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.85/1.03     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.85/1.03       ( ![E:$i]:
% 0.85/1.03         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.85/1.03  thf('29', plain,
% 0.85/1.03      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.85/1.03         ((zip_tseitin_0 @ X32 @ X33 @ X34 @ X35)
% 0.85/1.03          | (r2_hidden @ X32 @ X36)
% 0.85/1.03          | ((X36) != (k1_enumset1 @ X35 @ X34 @ X33)))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.85/1.03  thf('30', plain,
% 0.85/1.03      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.85/1.03         ((r2_hidden @ X32 @ (k1_enumset1 @ X35 @ X34 @ X33))
% 0.85/1.03          | (zip_tseitin_0 @ X32 @ X33 @ X34 @ X35))),
% 0.85/1.03      inference('simplify', [status(thm)], ['29'])).
% 0.85/1.03  thf('31', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.03         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.85/1.03          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.85/1.03      inference('sup+', [status(thm)], ['28', '30'])).
% 0.85/1.03  thf('32', plain,
% 0.85/1.03      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.85/1.03         (((X28) != (X27)) | ~ (zip_tseitin_0 @ X28 @ X29 @ X30 @ X27))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.85/1.03  thf('33', plain,
% 0.85/1.03      (![X27 : $i, X29 : $i, X30 : $i]:
% 0.85/1.03         ~ (zip_tseitin_0 @ X27 @ X29 @ X30 @ X27)),
% 0.85/1.03      inference('simplify', [status(thm)], ['32'])).
% 0.85/1.03  thf('34', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.85/1.03      inference('sup-', [status(thm)], ['31', '33'])).
% 0.85/1.03  thf('35', plain,
% 0.85/1.03      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.85/1.03      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.85/1.03  thf('36', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 0.85/1.03      inference('sup-', [status(thm)], ['34', '35'])).
% 0.85/1.03  thf('37', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.85/1.03      inference('sup-', [status(thm)], ['27', '36'])).
% 0.85/1.03  thf('38', plain, ($false), inference('sup-', [status(thm)], ['26', '37'])).
% 0.85/1.03  
% 0.85/1.03  % SZS output end Refutation
% 0.85/1.03  
% 0.85/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
