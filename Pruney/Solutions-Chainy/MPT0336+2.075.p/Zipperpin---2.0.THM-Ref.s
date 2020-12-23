%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.l6B1jC6iox

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:30 EST 2020

% Result     : Theorem 1.69s
% Output     : Refutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   59 (  72 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :   13
%              Number of atoms          :  349 ( 518 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('4',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X41 ) @ X42 )
      | ( r2_hidden @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t75_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) )).

thf('7',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_xboole_0 @ X24 @ X25 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t75_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_xboole_0 @ X21 @ X22 )
      | ( r1_xboole_0 @ X21 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('17',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k4_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) )
    = sk_B ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('22',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ X29 @ X30 )
      | ( r1_xboole_0 @ X29 @ ( k4_xboole_0 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup+',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('26',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_xboole_0 @ X24 @ X25 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t75_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('30',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('31',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) )
      | ~ ( r1_xboole_0 @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','32'])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('35',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['0','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.l6B1jC6iox
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:37:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.69/1.87  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.69/1.87  % Solved by: fo/fo7.sh
% 1.69/1.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.69/1.87  % done 3103 iterations in 1.424s
% 1.69/1.87  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.69/1.87  % SZS output start Refutation
% 1.69/1.87  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.69/1.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.69/1.87  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.69/1.87  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.69/1.87  thf(sk_B_type, type, sk_B: $i).
% 1.69/1.87  thf(sk_A_type, type, sk_A: $i).
% 1.69/1.87  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.69/1.87  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.69/1.87  thf(sk_D_type, type, sk_D: $i).
% 1.69/1.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.69/1.87  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.69/1.87  thf(t149_zfmisc_1, conjecture,
% 1.69/1.87    (![A:$i,B:$i,C:$i,D:$i]:
% 1.69/1.87     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.69/1.87         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.69/1.87       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.69/1.87  thf(zf_stmt_0, negated_conjecture,
% 1.69/1.87    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.69/1.87        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.69/1.87            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.69/1.87          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 1.69/1.87    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 1.69/1.87  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 1.69/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.87  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 1.69/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.87  thf(symmetry_r1_xboole_0, axiom,
% 1.69/1.87    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.69/1.87  thf('2', plain,
% 1.69/1.87      (![X2 : $i, X3 : $i]:
% 1.69/1.87         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.69/1.87      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.69/1.87  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 1.69/1.87      inference('sup-', [status(thm)], ['1', '2'])).
% 1.69/1.87  thf(l27_zfmisc_1, axiom,
% 1.69/1.87    (![A:$i,B:$i]:
% 1.69/1.87     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.69/1.87  thf('4', plain,
% 1.69/1.87      (![X41 : $i, X42 : $i]:
% 1.69/1.87         ((r1_xboole_0 @ (k1_tarski @ X41) @ X42) | (r2_hidden @ X41 @ X42))),
% 1.69/1.87      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.69/1.87  thf('5', plain,
% 1.69/1.87      (![X2 : $i, X3 : $i]:
% 1.69/1.87         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.69/1.87      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.69/1.87  thf('6', plain,
% 1.69/1.87      (![X0 : $i, X1 : $i]:
% 1.69/1.87         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 1.69/1.87      inference('sup-', [status(thm)], ['4', '5'])).
% 1.69/1.87  thf(t75_xboole_1, axiom,
% 1.69/1.87    (![A:$i,B:$i]:
% 1.69/1.87     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.69/1.87          ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ))).
% 1.69/1.87  thf('7', plain,
% 1.69/1.87      (![X24 : $i, X25 : $i]:
% 1.69/1.87         ((r1_xboole_0 @ X24 @ X25)
% 1.69/1.87          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ X25))),
% 1.69/1.87      inference('cnf', [status(esa)], [t75_xboole_1])).
% 1.69/1.87  thf('8', plain,
% 1.69/1.87      (![X0 : $i, X1 : $i]:
% 1.69/1.87         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.69/1.87          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 1.69/1.87      inference('sup-', [status(thm)], ['6', '7'])).
% 1.69/1.87  thf('9', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 1.69/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.87  thf(t74_xboole_1, axiom,
% 1.69/1.87    (![A:$i,B:$i,C:$i]:
% 1.69/1.87     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 1.69/1.87          ( r1_xboole_0 @ A @ B ) ) ))).
% 1.69/1.87  thf('10', plain,
% 1.69/1.87      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.69/1.87         (~ (r1_xboole_0 @ X21 @ X22)
% 1.69/1.87          | (r1_xboole_0 @ X21 @ (k3_xboole_0 @ X22 @ X23)))),
% 1.69/1.87      inference('cnf', [status(esa)], [t74_xboole_1])).
% 1.69/1.87  thf('11', plain,
% 1.69/1.87      (![X0 : $i]: (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_B @ X0))),
% 1.69/1.87      inference('sup-', [status(thm)], ['9', '10'])).
% 1.69/1.87  thf('12', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 1.69/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.87  thf(t3_xboole_0, axiom,
% 1.69/1.87    (![A:$i,B:$i]:
% 1.69/1.87     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.69/1.87            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.69/1.87       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.69/1.87            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.69/1.87  thf('13', plain,
% 1.69/1.87      (![X4 : $i, X6 : $i, X7 : $i]:
% 1.69/1.87         (~ (r2_hidden @ X6 @ X4)
% 1.69/1.87          | ~ (r2_hidden @ X6 @ X7)
% 1.69/1.87          | ~ (r1_xboole_0 @ X4 @ X7))),
% 1.69/1.87      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.69/1.87  thf('14', plain,
% 1.69/1.87      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 1.69/1.87      inference('sup-', [status(thm)], ['12', '13'])).
% 1.69/1.87  thf('15', plain,
% 1.69/1.87      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ X0))),
% 1.69/1.87      inference('sup-', [status(thm)], ['11', '14'])).
% 1.69/1.87  thf('16', plain, ((r1_xboole_0 @ sk_B @ (k1_tarski @ sk_D))),
% 1.69/1.87      inference('sup-', [status(thm)], ['8', '15'])).
% 1.69/1.87  thf(t83_xboole_1, axiom,
% 1.69/1.87    (![A:$i,B:$i]:
% 1.69/1.87     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.69/1.87  thf('17', plain,
% 1.69/1.87      (![X26 : $i, X27 : $i]:
% 1.69/1.87         (((k4_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_xboole_0 @ X26 @ X27))),
% 1.69/1.87      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.69/1.87  thf('18', plain, (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_D)) = (sk_B))),
% 1.69/1.87      inference('sup-', [status(thm)], ['16', '17'])).
% 1.69/1.87  thf('19', plain,
% 1.69/1.87      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 1.69/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.87  thf(commutativity_k3_xboole_0, axiom,
% 1.69/1.87    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.69/1.87  thf('20', plain,
% 1.69/1.87      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.69/1.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.69/1.87  thf('21', plain,
% 1.69/1.87      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 1.69/1.87      inference('demod', [status(thm)], ['19', '20'])).
% 1.69/1.87  thf(t85_xboole_1, axiom,
% 1.69/1.87    (![A:$i,B:$i,C:$i]:
% 1.69/1.87     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 1.69/1.87  thf('22', plain,
% 1.69/1.87      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.69/1.87         (~ (r1_tarski @ X29 @ X30)
% 1.69/1.87          | (r1_xboole_0 @ X29 @ (k4_xboole_0 @ X31 @ X30)))),
% 1.69/1.87      inference('cnf', [status(esa)], [t85_xboole_1])).
% 1.69/1.87  thf('23', plain,
% 1.69/1.87      (![X0 : $i]:
% 1.69/1.87         (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ 
% 1.69/1.87          (k4_xboole_0 @ X0 @ (k1_tarski @ sk_D)))),
% 1.69/1.87      inference('sup-', [status(thm)], ['21', '22'])).
% 1.69/1.87  thf('24', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_B)),
% 1.69/1.87      inference('sup+', [status(thm)], ['18', '23'])).
% 1.69/1.87  thf('25', plain,
% 1.69/1.87      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.69/1.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.69/1.87  thf('26', plain,
% 1.69/1.87      (![X24 : $i, X25 : $i]:
% 1.69/1.87         ((r1_xboole_0 @ X24 @ X25)
% 1.69/1.87          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ X25))),
% 1.69/1.87      inference('cnf', [status(esa)], [t75_xboole_1])).
% 1.69/1.87  thf('27', plain,
% 1.69/1.87      (![X0 : $i, X1 : $i]:
% 1.69/1.87         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 1.69/1.87          | (r1_xboole_0 @ X0 @ X1))),
% 1.69/1.87      inference('sup-', [status(thm)], ['25', '26'])).
% 1.69/1.87  thf('28', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 1.69/1.87      inference('sup-', [status(thm)], ['24', '27'])).
% 1.69/1.87  thf('29', plain,
% 1.69/1.87      (![X2 : $i, X3 : $i]:
% 1.69/1.87         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.69/1.87      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.69/1.87  thf('30', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 1.69/1.87      inference('sup-', [status(thm)], ['28', '29'])).
% 1.69/1.87  thf(t70_xboole_1, axiom,
% 1.69/1.87    (![A:$i,B:$i,C:$i]:
% 1.69/1.87     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 1.69/1.87            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 1.69/1.87       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 1.69/1.87            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 1.69/1.87  thf('31', plain,
% 1.69/1.87      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.69/1.87         ((r1_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19))
% 1.69/1.87          | ~ (r1_xboole_0 @ X17 @ X18)
% 1.69/1.87          | ~ (r1_xboole_0 @ X17 @ X19))),
% 1.69/1.87      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.69/1.87  thf('32', plain,
% 1.69/1.87      (![X0 : $i]:
% 1.69/1.87         (~ (r1_xboole_0 @ sk_B @ X0)
% 1.69/1.87          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 1.69/1.87      inference('sup-', [status(thm)], ['30', '31'])).
% 1.69/1.87  thf('33', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1))),
% 1.69/1.87      inference('sup-', [status(thm)], ['3', '32'])).
% 1.69/1.87  thf('34', plain,
% 1.69/1.87      (![X2 : $i, X3 : $i]:
% 1.69/1.87         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.69/1.87      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.69/1.87  thf('35', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 1.69/1.87      inference('sup-', [status(thm)], ['33', '34'])).
% 1.69/1.87  thf('36', plain, ($false), inference('demod', [status(thm)], ['0', '35'])).
% 1.69/1.87  
% 1.69/1.87  % SZS output end Refutation
% 1.69/1.87  
% 1.69/1.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
