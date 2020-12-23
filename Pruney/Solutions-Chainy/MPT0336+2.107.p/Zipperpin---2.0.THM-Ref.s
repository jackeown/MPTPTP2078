%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eMPAtnvuuE

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:34 EST 2020

% Result     : Theorem 5.29s
% Output     : Refutation 5.29s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 121 expanded)
%              Number of leaves         :   22 (  46 expanded)
%              Depth                    :   19
%              Number of atoms          :  501 ( 878 expanded)
%              Number of equality atoms :   15 (  20 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k4_xboole_0 @ X34 @ ( k1_tarski @ X35 ) )
        = X34 )
      | ( r2_hidden @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k4_xboole_0 @ X22 @ X23 )
        = X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_B )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_C_1 )
    = ( k3_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('14',plain,(
    r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
      | ~ ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ( r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
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

thf('20',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( r2_hidden @ sk_D @ ( k2_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['7','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('25',plain,(
    r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k4_xboole_0 @ X22 @ X23 )
        = X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('27',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) )
    = sk_B ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('30',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k4_xboole_0 @ X22 @ X23 )
        = X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('32',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ~ ( r1_tarski @ X6 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ X0 )
      | ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['27','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('37',plain,(
    r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t77_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('38',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_xboole_0 @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X17 @ ( k3_xboole_0 @ X18 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t77_xboole_1])).

thf('39',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('41',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('45',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k4_xboole_0 @ X22 @ X23 )
        = X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('47',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('50',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('52',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
      | ~ ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X2 )
      | ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['47','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('57',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['0','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eMPAtnvuuE
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:25:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.29/5.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.29/5.50  % Solved by: fo/fo7.sh
% 5.29/5.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.29/5.50  % done 12153 iterations in 5.046s
% 5.29/5.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.29/5.50  % SZS output start Refutation
% 5.29/5.50  thf(sk_B_type, type, sk_B: $i).
% 5.29/5.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 5.29/5.50  thf(sk_D_type, type, sk_D: $i).
% 5.29/5.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.29/5.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.29/5.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 5.29/5.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.29/5.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 5.29/5.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.29/5.50  thf(sk_A_type, type, sk_A: $i).
% 5.29/5.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.29/5.50  thf(t149_zfmisc_1, conjecture,
% 5.29/5.50    (![A:$i,B:$i,C:$i,D:$i]:
% 5.29/5.50     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 5.29/5.50         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 5.29/5.50       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 5.29/5.50  thf(zf_stmt_0, negated_conjecture,
% 5.29/5.50    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 5.29/5.50        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 5.29/5.50            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 5.29/5.50          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 5.29/5.50    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 5.29/5.50  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 5.29/5.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.29/5.50  thf(t65_zfmisc_1, axiom,
% 5.29/5.50    (![A:$i,B:$i]:
% 5.29/5.50     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 5.29/5.50       ( ~( r2_hidden @ B @ A ) ) ))).
% 5.29/5.50  thf('1', plain,
% 5.29/5.50      (![X34 : $i, X35 : $i]:
% 5.29/5.50         (((k4_xboole_0 @ X34 @ (k1_tarski @ X35)) = (X34))
% 5.29/5.50          | (r2_hidden @ X35 @ X34))),
% 5.29/5.50      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 5.29/5.50  thf(t79_xboole_1, axiom,
% 5.29/5.50    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 5.29/5.50  thf('2', plain,
% 5.29/5.50      (![X20 : $i, X21 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X21)),
% 5.29/5.50      inference('cnf', [status(esa)], [t79_xboole_1])).
% 5.29/5.50  thf(symmetry_r1_xboole_0, axiom,
% 5.29/5.50    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 5.29/5.50  thf('3', plain,
% 5.29/5.50      (![X0 : $i, X1 : $i]:
% 5.29/5.50         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 5.29/5.50      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 5.29/5.50  thf('4', plain,
% 5.29/5.50      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 5.29/5.50      inference('sup-', [status(thm)], ['2', '3'])).
% 5.29/5.50  thf('5', plain,
% 5.29/5.50      (![X0 : $i, X1 : $i]:
% 5.29/5.50         ((r1_xboole_0 @ (k1_tarski @ X1) @ X0) | (r2_hidden @ X1 @ X0))),
% 5.29/5.50      inference('sup+', [status(thm)], ['1', '4'])).
% 5.29/5.50  thf(t70_xboole_1, axiom,
% 5.29/5.50    (![A:$i,B:$i,C:$i]:
% 5.29/5.50     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 5.29/5.50            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 5.29/5.50       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 5.29/5.50            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 5.29/5.50  thf('6', plain,
% 5.29/5.50      (![X13 : $i, X14 : $i, X16 : $i]:
% 5.29/5.50         ((r1_xboole_0 @ X13 @ X14)
% 5.29/5.50          | ~ (r1_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X16)))),
% 5.29/5.50      inference('cnf', [status(esa)], [t70_xboole_1])).
% 5.29/5.50  thf('7', plain,
% 5.29/5.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.29/5.50         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 5.29/5.50          | (r1_xboole_0 @ (k1_tarski @ X2) @ X1))),
% 5.29/5.50      inference('sup-', [status(thm)], ['5', '6'])).
% 5.29/5.50  thf('8', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 5.29/5.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.29/5.50  thf(t83_xboole_1, axiom,
% 5.29/5.50    (![A:$i,B:$i]:
% 5.29/5.50     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 5.29/5.50  thf('9', plain,
% 5.29/5.50      (![X22 : $i, X23 : $i]:
% 5.29/5.50         (((k4_xboole_0 @ X22 @ X23) = (X22)) | ~ (r1_xboole_0 @ X22 @ X23))),
% 5.29/5.50      inference('cnf', [status(esa)], [t83_xboole_1])).
% 5.29/5.50  thf('10', plain, (((k4_xboole_0 @ sk_C_1 @ sk_B) = (sk_C_1))),
% 5.29/5.50      inference('sup-', [status(thm)], ['8', '9'])).
% 5.29/5.50  thf(t48_xboole_1, axiom,
% 5.29/5.50    (![A:$i,B:$i]:
% 5.29/5.50     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 5.29/5.50  thf('11', plain,
% 5.29/5.50      (![X11 : $i, X12 : $i]:
% 5.29/5.50         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 5.29/5.50           = (k3_xboole_0 @ X11 @ X12))),
% 5.29/5.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.29/5.50  thf('12', plain,
% 5.29/5.50      (((k4_xboole_0 @ sk_C_1 @ sk_C_1) = (k3_xboole_0 @ sk_C_1 @ sk_B))),
% 5.29/5.50      inference('sup+', [status(thm)], ['10', '11'])).
% 5.29/5.50  thf('13', plain,
% 5.29/5.50      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 5.29/5.50      inference('sup-', [status(thm)], ['2', '3'])).
% 5.29/5.50  thf('14', plain, ((r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_C_1 @ sk_B))),
% 5.29/5.50      inference('sup+', [status(thm)], ['12', '13'])).
% 5.29/5.50  thf('15', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 5.29/5.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.29/5.50  thf('16', plain,
% 5.29/5.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.29/5.50         ((r1_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 5.29/5.50          | ~ (r1_xboole_0 @ X13 @ X14)
% 5.29/5.50          | ~ (r1_xboole_0 @ X13 @ X15))),
% 5.29/5.50      inference('cnf', [status(esa)], [t70_xboole_1])).
% 5.29/5.50  thf('17', plain,
% 5.29/5.50      (![X0 : $i]:
% 5.29/5.50         (~ (r1_xboole_0 @ sk_C_1 @ X0)
% 5.29/5.50          | (r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ X0)))),
% 5.29/5.50      inference('sup-', [status(thm)], ['15', '16'])).
% 5.29/5.50  thf('18', plain,
% 5.29/5.50      ((r1_xboole_0 @ sk_C_1 @ 
% 5.29/5.50        (k2_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ sk_B)))),
% 5.29/5.50      inference('sup-', [status(thm)], ['14', '17'])).
% 5.29/5.50  thf('19', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 5.29/5.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.29/5.50  thf(t3_xboole_0, axiom,
% 5.29/5.50    (![A:$i,B:$i]:
% 5.29/5.50     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 5.29/5.50            ( r1_xboole_0 @ A @ B ) ) ) & 
% 5.29/5.50       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 5.29/5.50            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 5.29/5.50  thf('20', plain,
% 5.29/5.50      (![X2 : $i, X4 : $i, X5 : $i]:
% 5.29/5.50         (~ (r2_hidden @ X4 @ X2)
% 5.29/5.50          | ~ (r2_hidden @ X4 @ X5)
% 5.29/5.50          | ~ (r1_xboole_0 @ X2 @ X5))),
% 5.29/5.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 5.29/5.50  thf('21', plain,
% 5.29/5.50      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 5.29/5.50      inference('sup-', [status(thm)], ['19', '20'])).
% 5.29/5.50  thf('22', plain,
% 5.29/5.50      (~ (r2_hidden @ sk_D @ 
% 5.29/5.50          (k2_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ sk_B)))),
% 5.29/5.50      inference('sup-', [status(thm)], ['18', '21'])).
% 5.29/5.50  thf('23', plain, ((r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_B)),
% 5.29/5.50      inference('sup-', [status(thm)], ['7', '22'])).
% 5.29/5.50  thf('24', plain,
% 5.29/5.50      (![X0 : $i, X1 : $i]:
% 5.29/5.50         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 5.29/5.50      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 5.29/5.50  thf('25', plain, ((r1_xboole_0 @ sk_B @ (k1_tarski @ sk_D))),
% 5.29/5.50      inference('sup-', [status(thm)], ['23', '24'])).
% 5.29/5.50  thf('26', plain,
% 5.29/5.50      (![X22 : $i, X23 : $i]:
% 5.29/5.50         (((k4_xboole_0 @ X22 @ X23) = (X22)) | ~ (r1_xboole_0 @ X22 @ X23))),
% 5.29/5.50      inference('cnf', [status(esa)], [t83_xboole_1])).
% 5.29/5.50  thf('27', plain, (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_D)) = (sk_B))),
% 5.29/5.50      inference('sup-', [status(thm)], ['25', '26'])).
% 5.29/5.50  thf('28', plain,
% 5.29/5.50      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 5.29/5.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.29/5.50  thf('29', plain,
% 5.29/5.50      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 5.29/5.50      inference('sup-', [status(thm)], ['2', '3'])).
% 5.29/5.50  thf('30', plain,
% 5.29/5.50      (![X22 : $i, X23 : $i]:
% 5.29/5.50         (((k4_xboole_0 @ X22 @ X23) = (X22)) | ~ (r1_xboole_0 @ X22 @ X23))),
% 5.29/5.50      inference('cnf', [status(esa)], [t83_xboole_1])).
% 5.29/5.50  thf('31', plain,
% 5.29/5.50      (![X0 : $i, X1 : $i]:
% 5.29/5.50         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 5.29/5.50      inference('sup-', [status(thm)], ['29', '30'])).
% 5.29/5.50  thf(t106_xboole_1, axiom,
% 5.29/5.50    (![A:$i,B:$i,C:$i]:
% 5.29/5.50     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 5.29/5.50       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 5.29/5.50  thf('32', plain,
% 5.29/5.50      (![X6 : $i, X7 : $i, X8 : $i]:
% 5.29/5.50         ((r1_xboole_0 @ X6 @ X8)
% 5.29/5.50          | ~ (r1_tarski @ X6 @ (k4_xboole_0 @ X7 @ X8)))),
% 5.29/5.50      inference('cnf', [status(esa)], [t106_xboole_1])).
% 5.29/5.50  thf('33', plain,
% 5.29/5.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.29/5.50         (~ (r1_tarski @ X2 @ X0)
% 5.29/5.50          | (r1_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 5.29/5.50      inference('sup-', [status(thm)], ['31', '32'])).
% 5.29/5.50  thf('34', plain,
% 5.29/5.50      (![X0 : $i]:
% 5.29/5.50         (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 5.29/5.50          (k4_xboole_0 @ X0 @ (k1_tarski @ sk_D)))),
% 5.29/5.50      inference('sup-', [status(thm)], ['28', '33'])).
% 5.29/5.50  thf('35', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_B)),
% 5.29/5.50      inference('sup+', [status(thm)], ['27', '34'])).
% 5.29/5.50  thf('36', plain,
% 5.29/5.50      (![X0 : $i, X1 : $i]:
% 5.29/5.50         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 5.29/5.50      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 5.29/5.50  thf('37', plain, ((r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B))),
% 5.29/5.50      inference('sup-', [status(thm)], ['35', '36'])).
% 5.29/5.50  thf(t77_xboole_1, axiom,
% 5.29/5.50    (![A:$i,B:$i,C:$i]:
% 5.29/5.50     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 5.29/5.50          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 5.29/5.50  thf('38', plain,
% 5.29/5.50      (![X17 : $i, X18 : $i, X19 : $i]:
% 5.29/5.50         ((r1_xboole_0 @ X17 @ X18)
% 5.29/5.50          | ~ (r1_xboole_0 @ X17 @ (k3_xboole_0 @ X18 @ X19))
% 5.29/5.50          | ~ (r1_tarski @ X17 @ X19))),
% 5.29/5.50      inference('cnf', [status(esa)], [t77_xboole_1])).
% 5.29/5.50  thf('39', plain,
% 5.29/5.50      ((~ (r1_tarski @ sk_B @ sk_B) | (r1_xboole_0 @ sk_B @ sk_A))),
% 5.29/5.50      inference('sup-', [status(thm)], ['37', '38'])).
% 5.29/5.50  thf('40', plain,
% 5.29/5.50      (![X0 : $i, X1 : $i]:
% 5.29/5.50         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 5.29/5.50      inference('sup-', [status(thm)], ['29', '30'])).
% 5.29/5.50  thf(t36_xboole_1, axiom,
% 5.29/5.50    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 5.29/5.50  thf('41', plain,
% 5.29/5.50      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 5.29/5.50      inference('cnf', [status(esa)], [t36_xboole_1])).
% 5.29/5.50  thf('42', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 5.29/5.50      inference('sup+', [status(thm)], ['40', '41'])).
% 5.29/5.50  thf('43', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 5.29/5.50      inference('demod', [status(thm)], ['39', '42'])).
% 5.29/5.50  thf('44', plain,
% 5.29/5.50      (![X0 : $i, X1 : $i]:
% 5.29/5.50         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 5.29/5.50      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 5.29/5.50  thf('45', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 5.29/5.50      inference('sup-', [status(thm)], ['43', '44'])).
% 5.29/5.50  thf('46', plain,
% 5.29/5.50      (![X22 : $i, X23 : $i]:
% 5.29/5.50         (((k4_xboole_0 @ X22 @ X23) = (X22)) | ~ (r1_xboole_0 @ X22 @ X23))),
% 5.29/5.50      inference('cnf', [status(esa)], [t83_xboole_1])).
% 5.29/5.50  thf('47', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 5.29/5.50      inference('sup-', [status(thm)], ['45', '46'])).
% 5.29/5.50  thf('48', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 5.29/5.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.29/5.50  thf('49', plain,
% 5.29/5.50      (![X0 : $i, X1 : $i]:
% 5.29/5.50         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 5.29/5.50      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 5.29/5.50  thf('50', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 5.29/5.50      inference('sup-', [status(thm)], ['48', '49'])).
% 5.29/5.50  thf('51', plain,
% 5.29/5.50      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 5.29/5.50      inference('sup-', [status(thm)], ['2', '3'])).
% 5.29/5.50  thf('52', plain,
% 5.29/5.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.29/5.50         ((r1_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 5.29/5.50          | ~ (r1_xboole_0 @ X13 @ X14)
% 5.29/5.50          | ~ (r1_xboole_0 @ X13 @ X15))),
% 5.29/5.50      inference('cnf', [status(esa)], [t70_xboole_1])).
% 5.29/5.50  thf('53', plain,
% 5.29/5.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.29/5.50         (~ (r1_xboole_0 @ X0 @ X2)
% 5.29/5.50          | (r1_xboole_0 @ X0 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 5.29/5.50      inference('sup-', [status(thm)], ['51', '52'])).
% 5.29/5.50  thf('54', plain,
% 5.29/5.50      (![X0 : $i]:
% 5.29/5.50         (r1_xboole_0 @ sk_B @ 
% 5.29/5.50          (k2_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_C_1))),
% 5.29/5.50      inference('sup-', [status(thm)], ['50', '53'])).
% 5.29/5.50  thf('55', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1))),
% 5.29/5.50      inference('sup+', [status(thm)], ['47', '54'])).
% 5.29/5.50  thf('56', plain,
% 5.29/5.50      (![X0 : $i, X1 : $i]:
% 5.29/5.50         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 5.29/5.50      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 5.29/5.50  thf('57', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 5.29/5.50      inference('sup-', [status(thm)], ['55', '56'])).
% 5.29/5.50  thf('58', plain, ($false), inference('demod', [status(thm)], ['0', '57'])).
% 5.29/5.50  
% 5.29/5.50  % SZS output end Refutation
% 5.29/5.50  
% 5.29/5.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
