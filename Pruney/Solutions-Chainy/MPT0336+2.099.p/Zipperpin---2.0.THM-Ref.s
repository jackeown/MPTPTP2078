%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VK6FNHkiXE

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:33 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :   62 (  75 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :   16
%              Number of atoms          :  399 ( 601 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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

thf('1',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('5',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X32
        = ( k1_tarski @ X31 ) )
      | ( X32 = k1_xboole_0 )
      | ~ ( r1_tarski @ X32 @ ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('6',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
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

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('10',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X11 )
      | ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    r2_hidden @ sk_D_2 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X11 )
      | ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D_2 @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k1_tarski @ sk_D_2 ) )
    | ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','21'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('23',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('24',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( X20 != X19 )
      | ( r2_hidden @ X20 @ X21 )
      | ( X21
       != ( k2_tarski @ X22 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('25',plain,(
    ! [X19: $i,X22: $i] :
      ( r2_hidden @ X19 @ ( k2_tarski @ X22 @ X19 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','25'])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['22','26'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('28',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ( ( k3_xboole_0 @ X6 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('29',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('32',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
      | ~ ( r1_xboole_0 @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','34'])).

thf('36',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('37',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['0','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VK6FNHkiXE
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:28:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.05/1.28  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.05/1.28  % Solved by: fo/fo7.sh
% 1.05/1.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.28  % done 1351 iterations in 0.838s
% 1.05/1.28  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.05/1.28  % SZS output start Refutation
% 1.05/1.28  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.05/1.28  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.05/1.28  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.05/1.28  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.05/1.28  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.05/1.28  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.05/1.28  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.05/1.28  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.28  thf(sk_D_2_type, type, sk_D_2: $i).
% 1.05/1.28  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.05/1.28  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.05/1.28  thf(sk_B_type, type, sk_B: $i).
% 1.05/1.28  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.05/1.28  thf(t149_zfmisc_1, conjecture,
% 1.05/1.28    (![A:$i,B:$i,C:$i,D:$i]:
% 1.05/1.28     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.05/1.28         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.05/1.28       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.05/1.28  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.28    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.05/1.28        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.05/1.28            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.05/1.28          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 1.05/1.28    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 1.05/1.28  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf(symmetry_r1_xboole_0, axiom,
% 1.05/1.28    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.05/1.28  thf('2', plain,
% 1.05/1.28      (![X9 : $i, X10 : $i]:
% 1.05/1.28         ((r1_xboole_0 @ X9 @ X10) | ~ (r1_xboole_0 @ X10 @ X9))),
% 1.05/1.28      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.05/1.28  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 1.05/1.28      inference('sup-', [status(thm)], ['1', '2'])).
% 1.05/1.28  thf('4', plain,
% 1.05/1.28      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D_2))),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf(l3_zfmisc_1, axiom,
% 1.05/1.28    (![A:$i,B:$i]:
% 1.05/1.28     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 1.05/1.28       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 1.05/1.28  thf('5', plain,
% 1.05/1.28      (![X31 : $i, X32 : $i]:
% 1.05/1.28         (((X32) = (k1_tarski @ X31))
% 1.05/1.28          | ((X32) = (k1_xboole_0))
% 1.05/1.28          | ~ (r1_tarski @ X32 @ (k1_tarski @ X31)))),
% 1.05/1.28      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 1.05/1.28  thf('6', plain,
% 1.05/1.28      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.05/1.28        | ((k3_xboole_0 @ sk_A @ sk_B) = (k1_tarski @ sk_D_2)))),
% 1.05/1.28      inference('sup-', [status(thm)], ['4', '5'])).
% 1.05/1.28  thf('7', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf(t3_xboole_0, axiom,
% 1.05/1.28    (![A:$i,B:$i]:
% 1.05/1.28     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.05/1.28            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.05/1.28       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.05/1.28            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.05/1.28  thf('8', plain,
% 1.05/1.28      (![X11 : $i, X12 : $i]:
% 1.05/1.28         ((r1_xboole_0 @ X11 @ X12) | (r2_hidden @ (sk_C @ X12 @ X11) @ X12))),
% 1.05/1.28      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.05/1.28  thf(d4_xboole_0, axiom,
% 1.05/1.28    (![A:$i,B:$i,C:$i]:
% 1.05/1.28     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.05/1.28       ( ![D:$i]:
% 1.05/1.28         ( ( r2_hidden @ D @ C ) <=>
% 1.05/1.28           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.05/1.28  thf('9', plain,
% 1.05/1.28      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.05/1.28         (~ (r2_hidden @ X4 @ X3)
% 1.05/1.28          | (r2_hidden @ X4 @ X2)
% 1.05/1.28          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 1.05/1.28      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.05/1.28  thf('10', plain,
% 1.05/1.28      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.05/1.28         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 1.05/1.28      inference('simplify', [status(thm)], ['9'])).
% 1.05/1.28  thf('11', plain,
% 1.05/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.28         ((r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.05/1.28          | (r2_hidden @ (sk_C @ (k3_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 1.05/1.28      inference('sup-', [status(thm)], ['8', '10'])).
% 1.05/1.28  thf('12', plain,
% 1.05/1.28      (![X11 : $i, X12 : $i]:
% 1.05/1.28         ((r1_xboole_0 @ X11 @ X12) | (r2_hidden @ (sk_C @ X12 @ X11) @ X11))),
% 1.05/1.28      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.05/1.28  thf('13', plain,
% 1.05/1.28      (![X11 : $i, X13 : $i, X14 : $i]:
% 1.05/1.28         (~ (r2_hidden @ X13 @ X11)
% 1.05/1.28          | ~ (r2_hidden @ X13 @ X14)
% 1.05/1.28          | ~ (r1_xboole_0 @ X11 @ X14))),
% 1.05/1.28      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.05/1.28  thf('14', plain,
% 1.05/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.28         ((r1_xboole_0 @ X0 @ X1)
% 1.05/1.28          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.05/1.28          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 1.05/1.28      inference('sup-', [status(thm)], ['12', '13'])).
% 1.05/1.28  thf('15', plain,
% 1.05/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.28         ((r1_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0))
% 1.05/1.28          | ~ (r1_xboole_0 @ X1 @ X0)
% 1.05/1.28          | (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0)))),
% 1.05/1.28      inference('sup-', [status(thm)], ['11', '14'])).
% 1.05/1.28  thf('16', plain,
% 1.05/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.28         (~ (r1_xboole_0 @ X1 @ X0)
% 1.05/1.28          | (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0)))),
% 1.05/1.28      inference('simplify', [status(thm)], ['15'])).
% 1.05/1.28  thf('17', plain,
% 1.05/1.28      (![X0 : $i]: (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ X0 @ sk_B))),
% 1.05/1.28      inference('sup-', [status(thm)], ['7', '16'])).
% 1.05/1.28  thf('18', plain, ((r2_hidden @ sk_D_2 @ sk_C_1)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('19', plain,
% 1.05/1.28      (![X11 : $i, X13 : $i, X14 : $i]:
% 1.05/1.28         (~ (r2_hidden @ X13 @ X11)
% 1.05/1.28          | ~ (r2_hidden @ X13 @ X14)
% 1.05/1.28          | ~ (r1_xboole_0 @ X11 @ X14))),
% 1.05/1.28      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.05/1.28  thf('20', plain,
% 1.05/1.28      (![X0 : $i]:
% 1.05/1.28         (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D_2 @ X0))),
% 1.05/1.28      inference('sup-', [status(thm)], ['18', '19'])).
% 1.05/1.28  thf('21', plain,
% 1.05/1.28      (![X0 : $i]: ~ (r2_hidden @ sk_D_2 @ (k3_xboole_0 @ X0 @ sk_B))),
% 1.05/1.28      inference('sup-', [status(thm)], ['17', '20'])).
% 1.05/1.28  thf('22', plain,
% 1.05/1.28      ((~ (r2_hidden @ sk_D_2 @ (k1_tarski @ sk_D_2))
% 1.05/1.28        | ((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 1.05/1.28      inference('sup-', [status(thm)], ['6', '21'])).
% 1.05/1.28  thf(t69_enumset1, axiom,
% 1.05/1.28    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.05/1.28  thf('23', plain,
% 1.05/1.28      (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 1.05/1.28      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.05/1.28  thf(d2_tarski, axiom,
% 1.05/1.28    (![A:$i,B:$i,C:$i]:
% 1.05/1.28     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 1.05/1.28       ( ![D:$i]:
% 1.05/1.28         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 1.05/1.28  thf('24', plain,
% 1.05/1.28      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.05/1.28         (((X20) != (X19))
% 1.05/1.28          | (r2_hidden @ X20 @ X21)
% 1.05/1.28          | ((X21) != (k2_tarski @ X22 @ X19)))),
% 1.05/1.28      inference('cnf', [status(esa)], [d2_tarski])).
% 1.05/1.28  thf('25', plain,
% 1.05/1.28      (![X19 : $i, X22 : $i]: (r2_hidden @ X19 @ (k2_tarski @ X22 @ X19))),
% 1.05/1.28      inference('simplify', [status(thm)], ['24'])).
% 1.05/1.28  thf('26', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.05/1.28      inference('sup+', [status(thm)], ['23', '25'])).
% 1.05/1.28  thf('27', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 1.05/1.28      inference('demod', [status(thm)], ['22', '26'])).
% 1.05/1.28  thf(d7_xboole_0, axiom,
% 1.05/1.28    (![A:$i,B:$i]:
% 1.05/1.28     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.05/1.28       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.05/1.28  thf('28', plain,
% 1.05/1.28      (![X6 : $i, X8 : $i]:
% 1.05/1.28         ((r1_xboole_0 @ X6 @ X8) | ((k3_xboole_0 @ X6 @ X8) != (k1_xboole_0)))),
% 1.05/1.28      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.05/1.28  thf('29', plain,
% 1.05/1.28      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 1.05/1.28      inference('sup-', [status(thm)], ['27', '28'])).
% 1.05/1.28  thf('30', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 1.05/1.28      inference('simplify', [status(thm)], ['29'])).
% 1.05/1.28  thf('31', plain,
% 1.05/1.28      (![X9 : $i, X10 : $i]:
% 1.05/1.28         ((r1_xboole_0 @ X9 @ X10) | ~ (r1_xboole_0 @ X10 @ X9))),
% 1.05/1.28      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.05/1.28  thf('32', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 1.05/1.28      inference('sup-', [status(thm)], ['30', '31'])).
% 1.05/1.28  thf(t70_xboole_1, axiom,
% 1.05/1.28    (![A:$i,B:$i,C:$i]:
% 1.05/1.28     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 1.05/1.28            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 1.05/1.28       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 1.05/1.28            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 1.05/1.28  thf('33', plain,
% 1.05/1.28      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.05/1.28         ((r1_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 1.05/1.28          | ~ (r1_xboole_0 @ X15 @ X16)
% 1.05/1.28          | ~ (r1_xboole_0 @ X15 @ X17))),
% 1.05/1.28      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.05/1.28  thf('34', plain,
% 1.05/1.28      (![X0 : $i]:
% 1.05/1.28         (~ (r1_xboole_0 @ sk_B @ X0)
% 1.05/1.28          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 1.05/1.28      inference('sup-', [status(thm)], ['32', '33'])).
% 1.05/1.28  thf('35', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1))),
% 1.05/1.28      inference('sup-', [status(thm)], ['3', '34'])).
% 1.05/1.28  thf('36', plain,
% 1.05/1.28      (![X9 : $i, X10 : $i]:
% 1.05/1.28         ((r1_xboole_0 @ X9 @ X10) | ~ (r1_xboole_0 @ X10 @ X9))),
% 1.05/1.28      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.05/1.28  thf('37', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 1.05/1.28      inference('sup-', [status(thm)], ['35', '36'])).
% 1.05/1.28  thf('38', plain, ($false), inference('demod', [status(thm)], ['0', '37'])).
% 1.05/1.28  
% 1.05/1.28  % SZS output end Refutation
% 1.05/1.28  
% 1.05/1.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
