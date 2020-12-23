%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4nYLC8sz3r

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:23 EST 2020

% Result     : Theorem 5.34s
% Output     : Refutation 5.34s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 103 expanded)
%              Number of leaves         :   23 (  40 expanded)
%              Depth                    :   17
%              Number of atoms          :  509 ( 802 expanded)
%              Number of equality atoms :   25 (  32 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k4_xboole_0 @ X35 @ ( k1_tarski @ X36 ) )
        = X35 )
      | ( r2_hidden @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X25: $i,X27: $i] :
      ( ( r1_xboole_0 @ X25 @ X27 )
      | ( ( k4_xboole_0 @ X25 @ X27 )
       != X25 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('18',plain,(
    ! [X21: $i,X22: $i,X24: $i] :
      ( ( r1_xboole_0 @ X21 @ X22 )
      | ~ ( r1_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r1_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) )
      | ~ ( r1_xboole_0 @ X21 @ X22 )
      | ~ ( r1_xboole_0 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ( r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
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

thf('26',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( r2_hidden @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['19','28'])).

thf('30',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_xboole_0 @ X25 @ X26 )
        = X25 )
      | ~ ( r1_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('31',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B )
    = ( k1_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('32',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_xboole_0 @ X14 @ X16 )
      | ~ ( r1_tarski @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_tarski @ sk_D ) )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['11','33'])).

thf('35',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('36',plain,(
    r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_xboole_0 @ X25 @ X26 )
        = X25 )
      | ~ ( r1_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('38',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('39',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('40',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('44',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('45',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_xboole_0 @ X14 @ X16 )
      | ~ ( r1_tarski @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup+',[status(thm)],['42','49'])).

thf('51',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r1_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) )
      | ~ ( r1_xboole_0 @ X21 @ X22 )
      | ~ ( r1_xboole_0 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','52'])).

thf('54',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('55',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['0','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4nYLC8sz3r
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:19:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.34/5.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.34/5.61  % Solved by: fo/fo7.sh
% 5.34/5.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.34/5.61  % done 10319 iterations in 5.132s
% 5.34/5.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.34/5.61  % SZS output start Refutation
% 5.34/5.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 5.34/5.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.34/5.61  thf(sk_D_type, type, sk_D: $i).
% 5.34/5.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.34/5.61  thf(sk_B_type, type, sk_B: $i).
% 5.34/5.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.34/5.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.34/5.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.34/5.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 5.34/5.61  thf(sk_A_type, type, sk_A: $i).
% 5.34/5.61  thf(sk_C_1_type, type, sk_C_1: $i).
% 5.34/5.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.34/5.61  thf(t149_zfmisc_1, conjecture,
% 5.34/5.61    (![A:$i,B:$i,C:$i,D:$i]:
% 5.34/5.61     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 5.34/5.61         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 5.34/5.61       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 5.34/5.61  thf(zf_stmt_0, negated_conjecture,
% 5.34/5.61    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 5.34/5.61        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 5.34/5.61            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 5.34/5.61          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 5.34/5.61    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 5.34/5.61  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 5.34/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.34/5.61  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 5.34/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.34/5.61  thf(d7_xboole_0, axiom,
% 5.34/5.61    (![A:$i,B:$i]:
% 5.34/5.61     ( ( r1_xboole_0 @ A @ B ) <=>
% 5.34/5.61       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 5.34/5.61  thf('2', plain,
% 5.34/5.61      (![X2 : $i, X3 : $i]:
% 5.34/5.61         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 5.34/5.61      inference('cnf', [status(esa)], [d7_xboole_0])).
% 5.34/5.61  thf('3', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B) = (k1_xboole_0))),
% 5.34/5.61      inference('sup-', [status(thm)], ['1', '2'])).
% 5.34/5.61  thf(commutativity_k3_xboole_0, axiom,
% 5.34/5.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 5.34/5.61  thf('4', plain,
% 5.34/5.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.34/5.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.34/5.61  thf('5', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 5.34/5.61      inference('demod', [status(thm)], ['3', '4'])).
% 5.34/5.61  thf('6', plain,
% 5.34/5.61      (![X2 : $i, X4 : $i]:
% 5.34/5.61         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 5.34/5.61      inference('cnf', [status(esa)], [d7_xboole_0])).
% 5.34/5.61  thf('7', plain,
% 5.34/5.61      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_C_1))),
% 5.34/5.61      inference('sup-', [status(thm)], ['5', '6'])).
% 5.34/5.61  thf('8', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 5.34/5.61      inference('simplify', [status(thm)], ['7'])).
% 5.34/5.61  thf('9', plain,
% 5.34/5.61      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 5.34/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.34/5.61  thf('10', plain,
% 5.34/5.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.34/5.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.34/5.61  thf('11', plain,
% 5.34/5.61      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 5.34/5.61      inference('demod', [status(thm)], ['9', '10'])).
% 5.34/5.61  thf(t65_zfmisc_1, axiom,
% 5.34/5.61    (![A:$i,B:$i]:
% 5.34/5.61     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 5.34/5.61       ( ~( r2_hidden @ B @ A ) ) ))).
% 5.34/5.61  thf('12', plain,
% 5.34/5.61      (![X35 : $i, X36 : $i]:
% 5.34/5.61         (((k4_xboole_0 @ X35 @ (k1_tarski @ X36)) = (X35))
% 5.34/5.61          | (r2_hidden @ X36 @ X35))),
% 5.34/5.61      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 5.34/5.61  thf(t83_xboole_1, axiom,
% 5.34/5.61    (![A:$i,B:$i]:
% 5.34/5.61     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 5.34/5.61  thf('13', plain,
% 5.34/5.61      (![X25 : $i, X27 : $i]:
% 5.34/5.61         ((r1_xboole_0 @ X25 @ X27) | ((k4_xboole_0 @ X25 @ X27) != (X25)))),
% 5.34/5.61      inference('cnf', [status(esa)], [t83_xboole_1])).
% 5.34/5.61  thf('14', plain,
% 5.34/5.61      (![X0 : $i, X1 : $i]:
% 5.34/5.61         (((X0) != (X0))
% 5.34/5.61          | (r2_hidden @ X1 @ X0)
% 5.34/5.61          | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 5.34/5.61      inference('sup-', [status(thm)], ['12', '13'])).
% 5.34/5.61  thf('15', plain,
% 5.34/5.61      (![X0 : $i, X1 : $i]:
% 5.34/5.61         ((r1_xboole_0 @ X0 @ (k1_tarski @ X1)) | (r2_hidden @ X1 @ X0))),
% 5.34/5.61      inference('simplify', [status(thm)], ['14'])).
% 5.34/5.61  thf(symmetry_r1_xboole_0, axiom,
% 5.34/5.61    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 5.34/5.61  thf('16', plain,
% 5.34/5.61      (![X5 : $i, X6 : $i]:
% 5.34/5.61         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 5.34/5.61      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 5.34/5.61  thf('17', plain,
% 5.34/5.61      (![X0 : $i, X1 : $i]:
% 5.34/5.61         ((r2_hidden @ X0 @ X1) | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 5.34/5.61      inference('sup-', [status(thm)], ['15', '16'])).
% 5.34/5.61  thf(t70_xboole_1, axiom,
% 5.34/5.61    (![A:$i,B:$i,C:$i]:
% 5.34/5.61     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 5.34/5.61            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 5.34/5.61       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 5.34/5.61            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 5.34/5.61  thf('18', plain,
% 5.34/5.61      (![X21 : $i, X22 : $i, X24 : $i]:
% 5.34/5.61         ((r1_xboole_0 @ X21 @ X22)
% 5.34/5.61          | ~ (r1_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X24)))),
% 5.34/5.61      inference('cnf', [status(esa)], [t70_xboole_1])).
% 5.34/5.61  thf('19', plain,
% 5.34/5.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.34/5.61         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 5.34/5.61          | (r1_xboole_0 @ (k1_tarski @ X2) @ X1))),
% 5.34/5.61      inference('sup-', [status(thm)], ['17', '18'])).
% 5.34/5.61  thf('20', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 5.34/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.34/5.61  thf('21', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 5.34/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.34/5.61  thf('22', plain,
% 5.34/5.61      (![X21 : $i, X22 : $i, X23 : $i]:
% 5.34/5.61         ((r1_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23))
% 5.34/5.61          | ~ (r1_xboole_0 @ X21 @ X22)
% 5.34/5.61          | ~ (r1_xboole_0 @ X21 @ X23))),
% 5.34/5.61      inference('cnf', [status(esa)], [t70_xboole_1])).
% 5.34/5.61  thf('23', plain,
% 5.34/5.61      (![X0 : $i]:
% 5.34/5.61         (~ (r1_xboole_0 @ sk_C_1 @ X0)
% 5.34/5.61          | (r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ X0)))),
% 5.34/5.61      inference('sup-', [status(thm)], ['21', '22'])).
% 5.34/5.61  thf('24', plain, ((r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_B))),
% 5.34/5.61      inference('sup-', [status(thm)], ['20', '23'])).
% 5.34/5.61  thf('25', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 5.34/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.34/5.61  thf(t3_xboole_0, axiom,
% 5.34/5.61    (![A:$i,B:$i]:
% 5.34/5.61     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 5.34/5.61            ( r1_xboole_0 @ A @ B ) ) ) & 
% 5.34/5.61       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 5.34/5.61            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 5.34/5.61  thf('26', plain,
% 5.34/5.61      (![X7 : $i, X9 : $i, X10 : $i]:
% 5.34/5.61         (~ (r2_hidden @ X9 @ X7)
% 5.34/5.61          | ~ (r2_hidden @ X9 @ X10)
% 5.34/5.61          | ~ (r1_xboole_0 @ X7 @ X10))),
% 5.34/5.61      inference('cnf', [status(esa)], [t3_xboole_0])).
% 5.34/5.61  thf('27', plain,
% 5.34/5.61      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 5.34/5.61      inference('sup-', [status(thm)], ['25', '26'])).
% 5.34/5.61  thf('28', plain, (~ (r2_hidden @ sk_D @ (k2_xboole_0 @ sk_B @ sk_B))),
% 5.34/5.61      inference('sup-', [status(thm)], ['24', '27'])).
% 5.34/5.61  thf('29', plain, ((r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_B)),
% 5.34/5.61      inference('sup-', [status(thm)], ['19', '28'])).
% 5.34/5.61  thf('30', plain,
% 5.34/5.61      (![X25 : $i, X26 : $i]:
% 5.34/5.61         (((k4_xboole_0 @ X25 @ X26) = (X25)) | ~ (r1_xboole_0 @ X25 @ X26))),
% 5.34/5.61      inference('cnf', [status(esa)], [t83_xboole_1])).
% 5.34/5.61  thf('31', plain,
% 5.34/5.61      (((k4_xboole_0 @ (k1_tarski @ sk_D) @ sk_B) = (k1_tarski @ sk_D))),
% 5.34/5.61      inference('sup-', [status(thm)], ['29', '30'])).
% 5.34/5.61  thf(t106_xboole_1, axiom,
% 5.34/5.61    (![A:$i,B:$i,C:$i]:
% 5.34/5.61     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 5.34/5.61       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 5.34/5.61  thf('32', plain,
% 5.34/5.61      (![X14 : $i, X15 : $i, X16 : $i]:
% 5.34/5.61         ((r1_xboole_0 @ X14 @ X16)
% 5.34/5.61          | ~ (r1_tarski @ X14 @ (k4_xboole_0 @ X15 @ X16)))),
% 5.34/5.61      inference('cnf', [status(esa)], [t106_xboole_1])).
% 5.34/5.61  thf('33', plain,
% 5.34/5.61      (![X0 : $i]:
% 5.34/5.61         (~ (r1_tarski @ X0 @ (k1_tarski @ sk_D)) | (r1_xboole_0 @ X0 @ sk_B))),
% 5.34/5.61      inference('sup-', [status(thm)], ['31', '32'])).
% 5.34/5.61  thf('34', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_B)),
% 5.34/5.61      inference('sup-', [status(thm)], ['11', '33'])).
% 5.34/5.61  thf('35', plain,
% 5.34/5.61      (![X5 : $i, X6 : $i]:
% 5.34/5.61         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 5.34/5.61      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 5.34/5.61  thf('36', plain, ((r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_A))),
% 5.34/5.61      inference('sup-', [status(thm)], ['34', '35'])).
% 5.34/5.61  thf('37', plain,
% 5.34/5.61      (![X25 : $i, X26 : $i]:
% 5.34/5.61         (((k4_xboole_0 @ X25 @ X26) = (X25)) | ~ (r1_xboole_0 @ X25 @ X26))),
% 5.34/5.61      inference('cnf', [status(esa)], [t83_xboole_1])).
% 5.34/5.61  thf('38', plain,
% 5.34/5.61      (((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 5.34/5.61      inference('sup-', [status(thm)], ['36', '37'])).
% 5.34/5.61  thf(t48_xboole_1, axiom,
% 5.34/5.61    (![A:$i,B:$i]:
% 5.34/5.61     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 5.34/5.61  thf('39', plain,
% 5.34/5.61      (![X19 : $i, X20 : $i]:
% 5.34/5.61         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 5.34/5.61           = (k3_xboole_0 @ X19 @ X20))),
% 5.34/5.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.34/5.61  thf('40', plain,
% 5.34/5.61      (![X19 : $i, X20 : $i]:
% 5.34/5.61         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 5.34/5.61           = (k3_xboole_0 @ X19 @ X20))),
% 5.34/5.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.34/5.61  thf('41', plain,
% 5.34/5.61      (![X0 : $i, X1 : $i]:
% 5.34/5.61         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 5.34/5.61           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 5.34/5.61      inference('sup+', [status(thm)], ['39', '40'])).
% 5.34/5.61  thf('42', plain,
% 5.34/5.61      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 5.34/5.61      inference('demod', [status(thm)], ['38', '41'])).
% 5.34/5.61  thf('43', plain,
% 5.34/5.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.34/5.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.34/5.61  thf('44', plain,
% 5.34/5.61      (![X19 : $i, X20 : $i]:
% 5.34/5.61         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 5.34/5.61           = (k3_xboole_0 @ X19 @ X20))),
% 5.34/5.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.34/5.61  thf(t36_xboole_1, axiom,
% 5.34/5.61    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 5.34/5.61  thf('45', plain,
% 5.34/5.61      (![X17 : $i, X18 : $i]: (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X17)),
% 5.34/5.61      inference('cnf', [status(esa)], [t36_xboole_1])).
% 5.34/5.61  thf('46', plain,
% 5.34/5.61      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 5.34/5.61      inference('sup+', [status(thm)], ['44', '45'])).
% 5.34/5.61  thf('47', plain,
% 5.34/5.61      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 5.34/5.61      inference('sup+', [status(thm)], ['43', '46'])).
% 5.34/5.61  thf('48', plain,
% 5.34/5.61      (![X14 : $i, X15 : $i, X16 : $i]:
% 5.34/5.61         ((r1_xboole_0 @ X14 @ X16)
% 5.34/5.61          | ~ (r1_tarski @ X14 @ (k4_xboole_0 @ X15 @ X16)))),
% 5.34/5.61      inference('cnf', [status(esa)], [t106_xboole_1])).
% 5.34/5.61  thf('49', plain,
% 5.34/5.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.34/5.61         (r1_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)),
% 5.34/5.61      inference('sup-', [status(thm)], ['47', '48'])).
% 5.34/5.61  thf('50', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 5.34/5.61      inference('sup+', [status(thm)], ['42', '49'])).
% 5.34/5.61  thf('51', plain,
% 5.34/5.61      (![X21 : $i, X22 : $i, X23 : $i]:
% 5.34/5.61         ((r1_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23))
% 5.34/5.61          | ~ (r1_xboole_0 @ X21 @ X22)
% 5.34/5.61          | ~ (r1_xboole_0 @ X21 @ X23))),
% 5.34/5.61      inference('cnf', [status(esa)], [t70_xboole_1])).
% 5.34/5.61  thf('52', plain,
% 5.34/5.61      (![X0 : $i]:
% 5.34/5.61         (~ (r1_xboole_0 @ sk_B @ X0)
% 5.34/5.61          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 5.34/5.61      inference('sup-', [status(thm)], ['50', '51'])).
% 5.34/5.61  thf('53', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1))),
% 5.34/5.61      inference('sup-', [status(thm)], ['8', '52'])).
% 5.34/5.61  thf('54', plain,
% 5.34/5.61      (![X5 : $i, X6 : $i]:
% 5.34/5.61         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 5.34/5.61      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 5.34/5.61  thf('55', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 5.34/5.61      inference('sup-', [status(thm)], ['53', '54'])).
% 5.34/5.61  thf('56', plain, ($false), inference('demod', [status(thm)], ['0', '55'])).
% 5.34/5.61  
% 5.34/5.61  % SZS output end Refutation
% 5.34/5.61  
% 5.45/5.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
