%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GcjnPg0zal

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:30 EST 2020

% Result     : Theorem 1.01s
% Output     : Refutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :   70 (  86 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :   13
%              Number of atoms          :  438 ( 687 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_B @ sk_C_2 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('4',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X35 ) @ X36 )
      | ( r2_hidden @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ( r1_xboole_0 @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) )
      | ~ ( r1_xboole_0 @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_2 @ X0 )
      | ( r1_xboole_0 @ sk_C_2 @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_xboole_0 @ sk_C_2 @ ( k2_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    r2_hidden @ sk_D @ sk_C_2 ),
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
      ( ~ ( r1_xboole_0 @ sk_C_2 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( r2_hidden @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['6','15'])).

thf(t74_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_xboole_0 @ X21 @ X22 )
      | ( r1_xboole_0 @ X21 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
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

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 )
      | ( r1_xboole_0 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X8 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('26',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X24 @ X25 ) @ X25 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('29',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k4_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('34',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','36'])).

thf('38',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['24','37'])).

thf('39',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) )
      | ~ ( r1_xboole_0 @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['3','40'])).

thf('42',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('43',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['0','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GcjnPg0zal
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:05:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.01/1.26  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.01/1.26  % Solved by: fo/fo7.sh
% 1.01/1.26  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.01/1.26  % done 2456 iterations in 0.813s
% 1.01/1.26  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.01/1.26  % SZS output start Refutation
% 1.01/1.26  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.01/1.26  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.01/1.26  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.01/1.26  thf(sk_A_type, type, sk_A: $i).
% 1.01/1.26  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.01/1.26  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.01/1.26  thf(sk_B_type, type, sk_B: $i).
% 1.01/1.26  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.01/1.26  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.01/1.26  thf(sk_D_type, type, sk_D: $i).
% 1.01/1.26  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.01/1.26  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.01/1.26  thf(t149_zfmisc_1, conjecture,
% 1.01/1.26    (![A:$i,B:$i,C:$i,D:$i]:
% 1.01/1.26     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.01/1.26         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.01/1.26       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.01/1.26  thf(zf_stmt_0, negated_conjecture,
% 1.01/1.26    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.01/1.26        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.01/1.26            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.01/1.26          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 1.01/1.26    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 1.01/1.26  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 1.01/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.26  thf('1', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 1.01/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.26  thf(symmetry_r1_xboole_0, axiom,
% 1.01/1.26    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.01/1.26  thf('2', plain,
% 1.01/1.26      (![X2 : $i, X3 : $i]:
% 1.01/1.26         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.01/1.26      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.01/1.26  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C_2)),
% 1.01/1.26      inference('sup-', [status(thm)], ['1', '2'])).
% 1.01/1.26  thf(l27_zfmisc_1, axiom,
% 1.01/1.26    (![A:$i,B:$i]:
% 1.01/1.26     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.01/1.26  thf('4', plain,
% 1.01/1.26      (![X35 : $i, X36 : $i]:
% 1.01/1.26         ((r1_xboole_0 @ (k1_tarski @ X35) @ X36) | (r2_hidden @ X35 @ X36))),
% 1.01/1.26      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.01/1.26  thf(t70_xboole_1, axiom,
% 1.01/1.26    (![A:$i,B:$i,C:$i]:
% 1.01/1.26     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 1.01/1.26            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 1.01/1.26       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 1.01/1.26            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 1.01/1.26  thf('5', plain,
% 1.01/1.26      (![X17 : $i, X18 : $i, X20 : $i]:
% 1.01/1.26         ((r1_xboole_0 @ X17 @ X18)
% 1.01/1.26          | ~ (r1_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X20)))),
% 1.01/1.26      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.01/1.26  thf('6', plain,
% 1.01/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.26         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 1.01/1.26          | (r1_xboole_0 @ (k1_tarski @ X2) @ X1))),
% 1.01/1.26      inference('sup-', [status(thm)], ['4', '5'])).
% 1.01/1.26  thf('7', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 1.01/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.26  thf('8', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 1.01/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.26  thf('9', plain,
% 1.01/1.26      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.01/1.26         ((r1_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19))
% 1.01/1.26          | ~ (r1_xboole_0 @ X17 @ X18)
% 1.01/1.26          | ~ (r1_xboole_0 @ X17 @ X19))),
% 1.01/1.26      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.01/1.26  thf('10', plain,
% 1.01/1.26      (![X0 : $i]:
% 1.01/1.26         (~ (r1_xboole_0 @ sk_C_2 @ X0)
% 1.01/1.26          | (r1_xboole_0 @ sk_C_2 @ (k2_xboole_0 @ sk_B @ X0)))),
% 1.01/1.26      inference('sup-', [status(thm)], ['8', '9'])).
% 1.01/1.26  thf('11', plain, ((r1_xboole_0 @ sk_C_2 @ (k2_xboole_0 @ sk_B @ sk_B))),
% 1.01/1.26      inference('sup-', [status(thm)], ['7', '10'])).
% 1.01/1.26  thf('12', plain, ((r2_hidden @ sk_D @ sk_C_2)),
% 1.01/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.26  thf(t3_xboole_0, axiom,
% 1.01/1.26    (![A:$i,B:$i]:
% 1.01/1.26     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.01/1.26            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.01/1.26       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.01/1.26            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.01/1.26  thf('13', plain,
% 1.01/1.26      (![X4 : $i, X6 : $i, X7 : $i]:
% 1.01/1.26         (~ (r2_hidden @ X6 @ X4)
% 1.01/1.26          | ~ (r2_hidden @ X6 @ X7)
% 1.01/1.26          | ~ (r1_xboole_0 @ X4 @ X7))),
% 1.01/1.26      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.01/1.26  thf('14', plain,
% 1.01/1.26      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_2 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 1.01/1.26      inference('sup-', [status(thm)], ['12', '13'])).
% 1.01/1.26  thf('15', plain, (~ (r2_hidden @ sk_D @ (k2_xboole_0 @ sk_B @ sk_B))),
% 1.01/1.26      inference('sup-', [status(thm)], ['11', '14'])).
% 1.01/1.26  thf('16', plain, ((r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_B)),
% 1.01/1.26      inference('sup-', [status(thm)], ['6', '15'])).
% 1.01/1.26  thf(t74_xboole_1, axiom,
% 1.01/1.26    (![A:$i,B:$i,C:$i]:
% 1.01/1.26     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 1.01/1.26          ( r1_xboole_0 @ A @ B ) ) ))).
% 1.01/1.26  thf('17', plain,
% 1.01/1.26      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.01/1.26         (~ (r1_xboole_0 @ X21 @ X22)
% 1.01/1.26          | (r1_xboole_0 @ X21 @ (k3_xboole_0 @ X22 @ X23)))),
% 1.01/1.26      inference('cnf', [status(esa)], [t74_xboole_1])).
% 1.01/1.26  thf('18', plain,
% 1.01/1.26      (![X0 : $i]:
% 1.01/1.26         (r1_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ X0))),
% 1.01/1.26      inference('sup-', [status(thm)], ['16', '17'])).
% 1.01/1.26  thf('19', plain,
% 1.01/1.26      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 1.01/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.26  thf(commutativity_k3_xboole_0, axiom,
% 1.01/1.26    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.01/1.26  thf('20', plain,
% 1.01/1.26      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.01/1.26      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.01/1.26  thf('21', plain,
% 1.01/1.26      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 1.01/1.26      inference('demod', [status(thm)], ['19', '20'])).
% 1.01/1.26  thf(t63_xboole_1, axiom,
% 1.01/1.26    (![A:$i,B:$i,C:$i]:
% 1.01/1.26     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 1.01/1.26       ( r1_xboole_0 @ A @ C ) ))).
% 1.01/1.26  thf('22', plain,
% 1.01/1.26      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.01/1.26         (~ (r1_tarski @ X14 @ X15)
% 1.01/1.26          | ~ (r1_xboole_0 @ X15 @ X16)
% 1.01/1.26          | (r1_xboole_0 @ X14 @ X16))),
% 1.01/1.26      inference('cnf', [status(esa)], [t63_xboole_1])).
% 1.01/1.26  thf('23', plain,
% 1.01/1.26      (![X0 : $i]:
% 1.01/1.26         ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0)
% 1.01/1.26          | ~ (r1_xboole_0 @ (k1_tarski @ sk_D) @ X0))),
% 1.01/1.26      inference('sup-', [status(thm)], ['21', '22'])).
% 1.01/1.26  thf('24', plain,
% 1.01/1.26      (![X0 : $i]:
% 1.01/1.26         (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k3_xboole_0 @ sk_B @ X0))),
% 1.01/1.26      inference('sup-', [status(thm)], ['18', '23'])).
% 1.01/1.26  thf(t4_xboole_0, axiom,
% 1.01/1.26    (![A:$i,B:$i]:
% 1.01/1.26     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.01/1.26            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.01/1.26       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.01/1.26            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.01/1.26  thf('25', plain,
% 1.01/1.26      (![X8 : $i, X9 : $i]:
% 1.01/1.26         ((r1_xboole_0 @ X8 @ X9)
% 1.01/1.26          | (r2_hidden @ (sk_C_1 @ X9 @ X8) @ (k3_xboole_0 @ X8 @ X9)))),
% 1.01/1.26      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.01/1.26  thf(t79_xboole_1, axiom,
% 1.01/1.26    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.01/1.26  thf('26', plain,
% 1.01/1.26      (![X24 : $i, X25 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X24 @ X25) @ X25)),
% 1.01/1.26      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.01/1.26  thf('27', plain,
% 1.01/1.26      (![X2 : $i, X3 : $i]:
% 1.01/1.26         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.01/1.26      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.01/1.26  thf('28', plain,
% 1.01/1.26      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 1.01/1.26      inference('sup-', [status(thm)], ['26', '27'])).
% 1.01/1.26  thf(t83_xboole_1, axiom,
% 1.01/1.26    (![A:$i,B:$i]:
% 1.01/1.26     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.01/1.26  thf('29', plain,
% 1.01/1.26      (![X26 : $i, X27 : $i]:
% 1.01/1.26         (((k4_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_xboole_0 @ X26 @ X27))),
% 1.01/1.26      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.01/1.26  thf('30', plain,
% 1.01/1.26      (![X0 : $i, X1 : $i]:
% 1.01/1.26         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 1.01/1.26      inference('sup-', [status(thm)], ['28', '29'])).
% 1.01/1.26  thf(t48_xboole_1, axiom,
% 1.01/1.26    (![A:$i,B:$i]:
% 1.01/1.26     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.01/1.26  thf('31', plain,
% 1.01/1.26      (![X12 : $i, X13 : $i]:
% 1.01/1.26         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 1.01/1.26           = (k3_xboole_0 @ X12 @ X13))),
% 1.01/1.26      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.01/1.26  thf('32', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.01/1.26      inference('sup+', [status(thm)], ['30', '31'])).
% 1.01/1.26  thf('33', plain,
% 1.01/1.26      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.01/1.26      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.01/1.26  thf('34', plain,
% 1.01/1.26      (![X8 : $i, X10 : $i, X11 : $i]:
% 1.01/1.26         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 1.01/1.26          | ~ (r1_xboole_0 @ X8 @ X11))),
% 1.01/1.26      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.01/1.26  thf('35', plain,
% 1.01/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.26         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.01/1.26          | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.01/1.26      inference('sup-', [status(thm)], ['33', '34'])).
% 1.01/1.26  thf('36', plain,
% 1.01/1.26      (![X0 : $i, X1 : $i]:
% 1.01/1.26         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 1.01/1.26      inference('sup-', [status(thm)], ['32', '35'])).
% 1.01/1.26  thf('37', plain,
% 1.01/1.26      (![X0 : $i, X1 : $i]:
% 1.01/1.26         ((r1_xboole_0 @ X1 @ X0)
% 1.01/1.26          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 1.01/1.26      inference('sup-', [status(thm)], ['25', '36'])).
% 1.01/1.26  thf('38', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 1.01/1.26      inference('sup-', [status(thm)], ['24', '37'])).
% 1.01/1.26  thf('39', plain,
% 1.01/1.26      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.01/1.26         ((r1_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19))
% 1.01/1.26          | ~ (r1_xboole_0 @ X17 @ X18)
% 1.01/1.26          | ~ (r1_xboole_0 @ X17 @ X19))),
% 1.01/1.26      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.01/1.26  thf('40', plain,
% 1.01/1.26      (![X0 : $i]:
% 1.01/1.26         (~ (r1_xboole_0 @ sk_B @ X0)
% 1.01/1.26          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 1.01/1.26      inference('sup-', [status(thm)], ['38', '39'])).
% 1.01/1.26  thf('41', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_2))),
% 1.01/1.26      inference('sup-', [status(thm)], ['3', '40'])).
% 1.01/1.26  thf('42', plain,
% 1.01/1.26      (![X2 : $i, X3 : $i]:
% 1.01/1.26         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.01/1.26      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.01/1.26  thf('43', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 1.01/1.26      inference('sup-', [status(thm)], ['41', '42'])).
% 1.01/1.26  thf('44', plain, ($false), inference('demod', [status(thm)], ['0', '43'])).
% 1.01/1.26  
% 1.01/1.26  % SZS output end Refutation
% 1.01/1.26  
% 1.01/1.27  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
