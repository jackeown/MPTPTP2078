%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.v0wilMm9TS

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:32 EST 2020

% Result     : Theorem 2.21s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 102 expanded)
%              Number of leaves         :   22 (  40 expanded)
%              Depth                    :   18
%              Number of atoms          :  489 ( 757 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf('4',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k4_xboole_0 @ X29 @ ( k1_tarski @ X30 ) )
        = X29 )
      | ( r2_hidden @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k4_xboole_0 @ X22 @ X23 )
        = X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('16',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_B )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('18',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('19',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
      | ~ ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,(
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

thf('24',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( r2_hidden @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['13','26'])).

thf('28',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k4_xboole_0 @ X22 @ X23 )
        = X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('29',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B )
    = ( k1_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_tarski @ sk_D ) )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['6','31'])).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('34',plain,(
    r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k4_xboole_0 @ X22 @ X23 )
        = X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('36',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t74_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf('43',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_xboole_0 @ X17 @ X18 )
      | ( r1_xboole_0 @ X17 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('48',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
      | ~ ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','50'])).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('53',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['0','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.v0wilMm9TS
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:55:40 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 2.21/2.39  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.21/2.39  % Solved by: fo/fo7.sh
% 2.21/2.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.21/2.39  % done 4642 iterations in 1.954s
% 2.21/2.39  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.21/2.39  % SZS output start Refutation
% 2.21/2.39  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.21/2.39  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.21/2.39  thf(sk_B_type, type, sk_B: $i).
% 2.21/2.39  thf(sk_D_type, type, sk_D: $i).
% 2.21/2.39  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.21/2.39  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.21/2.39  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.21/2.39  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.21/2.39  thf(sk_A_type, type, sk_A: $i).
% 2.21/2.39  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.21/2.39  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.21/2.39  thf(t149_zfmisc_1, conjecture,
% 2.21/2.39    (![A:$i,B:$i,C:$i,D:$i]:
% 2.21/2.39     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 2.21/2.39         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 2.21/2.39       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 2.21/2.39  thf(zf_stmt_0, negated_conjecture,
% 2.21/2.39    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.21/2.39        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 2.21/2.39            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 2.21/2.39          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 2.21/2.39    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 2.21/2.39  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 2.21/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.39  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 2.21/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.39  thf(symmetry_r1_xboole_0, axiom,
% 2.21/2.39    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 2.21/2.39  thf('2', plain,
% 2.21/2.39      (![X2 : $i, X3 : $i]:
% 2.21/2.39         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 2.21/2.39      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.21/2.39  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 2.21/2.39      inference('sup-', [status(thm)], ['1', '2'])).
% 2.21/2.39  thf('4', plain,
% 2.21/2.39      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 2.21/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.39  thf(commutativity_k3_xboole_0, axiom,
% 2.21/2.39    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.21/2.39  thf('5', plain,
% 2.21/2.39      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.21/2.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.21/2.39  thf('6', plain,
% 2.21/2.39      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 2.21/2.39      inference('demod', [status(thm)], ['4', '5'])).
% 2.21/2.39  thf(t65_zfmisc_1, axiom,
% 2.21/2.39    (![A:$i,B:$i]:
% 2.21/2.39     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 2.21/2.39       ( ~( r2_hidden @ B @ A ) ) ))).
% 2.21/2.39  thf('7', plain,
% 2.21/2.39      (![X29 : $i, X30 : $i]:
% 2.21/2.39         (((k4_xboole_0 @ X29 @ (k1_tarski @ X30)) = (X29))
% 2.21/2.39          | (r2_hidden @ X30 @ X29))),
% 2.21/2.39      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 2.21/2.39  thf(t79_xboole_1, axiom,
% 2.21/2.39    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 2.21/2.39  thf('8', plain,
% 2.21/2.39      (![X20 : $i, X21 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X21)),
% 2.21/2.39      inference('cnf', [status(esa)], [t79_xboole_1])).
% 2.21/2.39  thf('9', plain,
% 2.21/2.39      (![X2 : $i, X3 : $i]:
% 2.21/2.39         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 2.21/2.39      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.21/2.39  thf('10', plain,
% 2.21/2.39      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 2.21/2.39      inference('sup-', [status(thm)], ['8', '9'])).
% 2.21/2.39  thf('11', plain,
% 2.21/2.39      (![X0 : $i, X1 : $i]:
% 2.21/2.39         ((r1_xboole_0 @ (k1_tarski @ X1) @ X0) | (r2_hidden @ X1 @ X0))),
% 2.21/2.39      inference('sup+', [status(thm)], ['7', '10'])).
% 2.21/2.39  thf(t70_xboole_1, axiom,
% 2.21/2.39    (![A:$i,B:$i,C:$i]:
% 2.21/2.39     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 2.21/2.39            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 2.21/2.39       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 2.21/2.39            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 2.21/2.39  thf('12', plain,
% 2.21/2.39      (![X13 : $i, X14 : $i, X16 : $i]:
% 2.21/2.39         ((r1_xboole_0 @ X13 @ X14)
% 2.21/2.39          | ~ (r1_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X16)))),
% 2.21/2.39      inference('cnf', [status(esa)], [t70_xboole_1])).
% 2.21/2.39  thf('13', plain,
% 2.21/2.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.21/2.39         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 2.21/2.39          | (r1_xboole_0 @ (k1_tarski @ X2) @ X1))),
% 2.21/2.39      inference('sup-', [status(thm)], ['11', '12'])).
% 2.21/2.39  thf('14', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 2.21/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.39  thf(t83_xboole_1, axiom,
% 2.21/2.39    (![A:$i,B:$i]:
% 2.21/2.39     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.21/2.39  thf('15', plain,
% 2.21/2.39      (![X22 : $i, X23 : $i]:
% 2.21/2.39         (((k4_xboole_0 @ X22 @ X23) = (X22)) | ~ (r1_xboole_0 @ X22 @ X23))),
% 2.21/2.39      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.21/2.39  thf('16', plain, (((k4_xboole_0 @ sk_C_1 @ sk_B) = (sk_C_1))),
% 2.21/2.39      inference('sup-', [status(thm)], ['14', '15'])).
% 2.21/2.39  thf('17', plain,
% 2.21/2.39      (![X20 : $i, X21 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X21)),
% 2.21/2.39      inference('cnf', [status(esa)], [t79_xboole_1])).
% 2.21/2.39  thf('18', plain,
% 2.21/2.39      (![X20 : $i, X21 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X21)),
% 2.21/2.39      inference('cnf', [status(esa)], [t79_xboole_1])).
% 2.21/2.39  thf('19', plain,
% 2.21/2.39      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.21/2.39         ((r1_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 2.21/2.39          | ~ (r1_xboole_0 @ X13 @ X14)
% 2.21/2.39          | ~ (r1_xboole_0 @ X13 @ X15))),
% 2.21/2.39      inference('cnf', [status(esa)], [t70_xboole_1])).
% 2.21/2.39  thf('20', plain,
% 2.21/2.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.21/2.39         (~ (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 2.21/2.39          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 2.21/2.39      inference('sup-', [status(thm)], ['18', '19'])).
% 2.21/2.39  thf('21', plain,
% 2.21/2.39      (![X0 : $i, X1 : $i]:
% 2.21/2.39         (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X0))),
% 2.21/2.39      inference('sup-', [status(thm)], ['17', '20'])).
% 2.21/2.39  thf('22', plain, ((r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_B))),
% 2.21/2.39      inference('sup+', [status(thm)], ['16', '21'])).
% 2.21/2.39  thf('23', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 2.21/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.39  thf(t3_xboole_0, axiom,
% 2.21/2.39    (![A:$i,B:$i]:
% 2.21/2.39     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 2.21/2.39            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.21/2.39       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.21/2.39            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 2.21/2.39  thf('24', plain,
% 2.21/2.39      (![X4 : $i, X6 : $i, X7 : $i]:
% 2.21/2.39         (~ (r2_hidden @ X6 @ X4)
% 2.21/2.39          | ~ (r2_hidden @ X6 @ X7)
% 2.21/2.39          | ~ (r1_xboole_0 @ X4 @ X7))),
% 2.21/2.39      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.21/2.39  thf('25', plain,
% 2.21/2.39      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 2.21/2.39      inference('sup-', [status(thm)], ['23', '24'])).
% 2.21/2.39  thf('26', plain, (~ (r2_hidden @ sk_D @ (k2_xboole_0 @ sk_B @ sk_B))),
% 2.21/2.39      inference('sup-', [status(thm)], ['22', '25'])).
% 2.21/2.39  thf('27', plain, ((r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_B)),
% 2.21/2.39      inference('sup-', [status(thm)], ['13', '26'])).
% 2.21/2.39  thf('28', plain,
% 2.21/2.39      (![X22 : $i, X23 : $i]:
% 2.21/2.39         (((k4_xboole_0 @ X22 @ X23) = (X22)) | ~ (r1_xboole_0 @ X22 @ X23))),
% 2.21/2.39      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.21/2.39  thf('29', plain,
% 2.21/2.39      (((k4_xboole_0 @ (k1_tarski @ sk_D) @ sk_B) = (k1_tarski @ sk_D))),
% 2.21/2.39      inference('sup-', [status(thm)], ['27', '28'])).
% 2.21/2.39  thf(t106_xboole_1, axiom,
% 2.21/2.39    (![A:$i,B:$i,C:$i]:
% 2.21/2.39     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 2.21/2.39       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 2.21/2.39  thf('30', plain,
% 2.21/2.39      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.21/2.39         ((r1_xboole_0 @ X8 @ X10)
% 2.21/2.39          | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X10)))),
% 2.21/2.39      inference('cnf', [status(esa)], [t106_xboole_1])).
% 2.21/2.39  thf('31', plain,
% 2.21/2.39      (![X0 : $i]:
% 2.21/2.39         (~ (r1_tarski @ X0 @ (k1_tarski @ sk_D)) | (r1_xboole_0 @ X0 @ sk_B))),
% 2.21/2.39      inference('sup-', [status(thm)], ['29', '30'])).
% 2.21/2.39  thf('32', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_B)),
% 2.21/2.39      inference('sup-', [status(thm)], ['6', '31'])).
% 2.21/2.39  thf('33', plain,
% 2.21/2.39      (![X2 : $i, X3 : $i]:
% 2.21/2.39         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 2.21/2.39      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.21/2.39  thf('34', plain, ((r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_A))),
% 2.21/2.39      inference('sup-', [status(thm)], ['32', '33'])).
% 2.21/2.39  thf('35', plain,
% 2.21/2.39      (![X22 : $i, X23 : $i]:
% 2.21/2.39         (((k4_xboole_0 @ X22 @ X23) = (X22)) | ~ (r1_xboole_0 @ X22 @ X23))),
% 2.21/2.39      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.21/2.39  thf('36', plain,
% 2.21/2.39      (((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 2.21/2.39      inference('sup-', [status(thm)], ['34', '35'])).
% 2.21/2.39  thf(t48_xboole_1, axiom,
% 2.21/2.39    (![A:$i,B:$i]:
% 2.21/2.39     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.21/2.39  thf('37', plain,
% 2.21/2.39      (![X11 : $i, X12 : $i]:
% 2.21/2.39         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 2.21/2.39           = (k3_xboole_0 @ X11 @ X12))),
% 2.21/2.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.21/2.39  thf('38', plain,
% 2.21/2.39      (![X11 : $i, X12 : $i]:
% 2.21/2.39         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 2.21/2.39           = (k3_xboole_0 @ X11 @ X12))),
% 2.21/2.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.21/2.39  thf('39', plain,
% 2.21/2.39      (![X0 : $i, X1 : $i]:
% 2.21/2.39         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 2.21/2.39           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.21/2.39      inference('sup+', [status(thm)], ['37', '38'])).
% 2.21/2.39  thf('40', plain,
% 2.21/2.39      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 2.21/2.39      inference('demod', [status(thm)], ['36', '39'])).
% 2.21/2.39  thf('41', plain,
% 2.21/2.39      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.21/2.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.21/2.39  thf('42', plain,
% 2.21/2.39      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 2.21/2.39      inference('sup-', [status(thm)], ['8', '9'])).
% 2.21/2.39  thf(t74_xboole_1, axiom,
% 2.21/2.39    (![A:$i,B:$i,C:$i]:
% 2.21/2.39     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 2.21/2.39          ( r1_xboole_0 @ A @ B ) ) ))).
% 2.21/2.39  thf('43', plain,
% 2.21/2.39      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.21/2.39         (~ (r1_xboole_0 @ X17 @ X18)
% 2.21/2.39          | (r1_xboole_0 @ X17 @ (k3_xboole_0 @ X18 @ X19)))),
% 2.21/2.39      inference('cnf', [status(esa)], [t74_xboole_1])).
% 2.21/2.39  thf('44', plain,
% 2.21/2.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.21/2.39         (r1_xboole_0 @ X0 @ (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))),
% 2.21/2.39      inference('sup-', [status(thm)], ['42', '43'])).
% 2.21/2.39  thf('45', plain,
% 2.21/2.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.21/2.39         (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.21/2.39      inference('sup+', [status(thm)], ['41', '44'])).
% 2.21/2.39  thf('46', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 2.21/2.39      inference('sup+', [status(thm)], ['40', '45'])).
% 2.21/2.39  thf('47', plain,
% 2.21/2.39      (![X2 : $i, X3 : $i]:
% 2.21/2.39         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 2.21/2.39      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.21/2.39  thf('48', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 2.21/2.39      inference('sup-', [status(thm)], ['46', '47'])).
% 2.21/2.39  thf('49', plain,
% 2.21/2.39      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.21/2.39         ((r1_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 2.21/2.39          | ~ (r1_xboole_0 @ X13 @ X14)
% 2.21/2.39          | ~ (r1_xboole_0 @ X13 @ X15))),
% 2.21/2.39      inference('cnf', [status(esa)], [t70_xboole_1])).
% 2.21/2.39  thf('50', plain,
% 2.21/2.39      (![X0 : $i]:
% 2.21/2.39         (~ (r1_xboole_0 @ sk_B @ X0)
% 2.21/2.39          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 2.21/2.39      inference('sup-', [status(thm)], ['48', '49'])).
% 2.21/2.39  thf('51', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1))),
% 2.21/2.39      inference('sup-', [status(thm)], ['3', '50'])).
% 2.21/2.39  thf('52', plain,
% 2.21/2.39      (![X2 : $i, X3 : $i]:
% 2.21/2.39         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 2.21/2.39      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.21/2.39  thf('53', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 2.21/2.39      inference('sup-', [status(thm)], ['51', '52'])).
% 2.21/2.39  thf('54', plain, ($false), inference('demod', [status(thm)], ['0', '53'])).
% 2.21/2.39  
% 2.21/2.39  % SZS output end Refutation
% 2.21/2.39  
% 2.25/2.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
