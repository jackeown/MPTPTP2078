%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hoR6g6Iwpb

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:30 EST 2020

% Result     : Theorem 4.19s
% Output     : Refutation 4.19s
% Verified   : 
% Statistics : Number of formulae       :   74 (  97 expanded)
%              Number of leaves         :   22 (  38 expanded)
%              Depth                    :   17
%              Number of atoms          :  460 ( 746 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('3',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('4',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X32 ) @ X33 )
      | ( r2_hidden @ X32 @ X33 ) ) ),
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
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B )
    = ( k1_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('19',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X12 @ X14 )
      | ~ ( r1_tarski @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_tarski @ sk_D ) )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['3','20'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('23',plain,(
    r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k4_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('25',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('27',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('31',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X24 @ X25 ) @ X25 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t74_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_xboole_0 @ X21 @ X22 )
      | ( r1_xboole_0 @ X21 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','35'])).

thf('37',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['29','36'])).

thf('38',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k4_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('39',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('42',plain,(
    r1_xboole_0 @ sk_B @ sk_C_2 ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('44',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) )
      | ~ ( r1_xboole_0 @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X2 )
      | ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['39','46'])).

thf('48',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('49',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['0','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hoR6g6Iwpb
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:23:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 4.19/4.42  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.19/4.42  % Solved by: fo/fo7.sh
% 4.19/4.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.19/4.42  % done 9148 iterations in 3.962s
% 4.19/4.42  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.19/4.42  % SZS output start Refutation
% 4.19/4.42  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 4.19/4.42  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.19/4.42  thf(sk_B_type, type, sk_B: $i).
% 4.19/4.42  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.19/4.42  thf(sk_C_2_type, type, sk_C_2: $i).
% 4.19/4.42  thf(sk_A_type, type, sk_A: $i).
% 4.19/4.42  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.19/4.42  thf(sk_D_type, type, sk_D: $i).
% 4.19/4.42  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.19/4.42  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.19/4.42  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 4.19/4.42  thf(t149_zfmisc_1, conjecture,
% 4.19/4.42    (![A:$i,B:$i,C:$i,D:$i]:
% 4.19/4.42     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 4.19/4.42         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 4.19/4.42       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 4.19/4.42  thf(zf_stmt_0, negated_conjecture,
% 4.19/4.42    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 4.19/4.42        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 4.19/4.42            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 4.19/4.42          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 4.19/4.42    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 4.19/4.42  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('1', plain,
% 4.19/4.42      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf(commutativity_k3_xboole_0, axiom,
% 4.19/4.42    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 4.19/4.42  thf('2', plain,
% 4.19/4.42      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.19/4.42      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.19/4.42  thf('3', plain,
% 4.19/4.42      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 4.19/4.42      inference('demod', [status(thm)], ['1', '2'])).
% 4.19/4.42  thf(l27_zfmisc_1, axiom,
% 4.19/4.42    (![A:$i,B:$i]:
% 4.19/4.42     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 4.19/4.42  thf('4', plain,
% 4.19/4.42      (![X32 : $i, X33 : $i]:
% 4.19/4.42         ((r1_xboole_0 @ (k1_tarski @ X32) @ X33) | (r2_hidden @ X32 @ X33))),
% 4.19/4.42      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 4.19/4.42  thf(t70_xboole_1, axiom,
% 4.19/4.42    (![A:$i,B:$i,C:$i]:
% 4.19/4.42     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 4.19/4.42            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 4.19/4.42       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 4.19/4.42            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 4.19/4.42  thf('5', plain,
% 4.19/4.42      (![X17 : $i, X18 : $i, X20 : $i]:
% 4.19/4.42         ((r1_xboole_0 @ X17 @ X18)
% 4.19/4.42          | ~ (r1_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X20)))),
% 4.19/4.42      inference('cnf', [status(esa)], [t70_xboole_1])).
% 4.19/4.42  thf('6', plain,
% 4.19/4.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.19/4.42         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 4.19/4.42          | (r1_xboole_0 @ (k1_tarski @ X2) @ X1))),
% 4.19/4.42      inference('sup-', [status(thm)], ['4', '5'])).
% 4.19/4.42  thf('7', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('8', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('9', plain,
% 4.19/4.42      (![X17 : $i, X18 : $i, X19 : $i]:
% 4.19/4.42         ((r1_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19))
% 4.19/4.42          | ~ (r1_xboole_0 @ X17 @ X18)
% 4.19/4.42          | ~ (r1_xboole_0 @ X17 @ X19))),
% 4.19/4.42      inference('cnf', [status(esa)], [t70_xboole_1])).
% 4.19/4.42  thf('10', plain,
% 4.19/4.42      (![X0 : $i]:
% 4.19/4.42         (~ (r1_xboole_0 @ sk_C_2 @ X0)
% 4.19/4.42          | (r1_xboole_0 @ sk_C_2 @ (k2_xboole_0 @ sk_B @ X0)))),
% 4.19/4.42      inference('sup-', [status(thm)], ['8', '9'])).
% 4.19/4.42  thf('11', plain, ((r1_xboole_0 @ sk_C_2 @ (k2_xboole_0 @ sk_B @ sk_B))),
% 4.19/4.42      inference('sup-', [status(thm)], ['7', '10'])).
% 4.19/4.42  thf('12', plain, ((r2_hidden @ sk_D @ sk_C_2)),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf(t3_xboole_0, axiom,
% 4.19/4.42    (![A:$i,B:$i]:
% 4.19/4.42     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 4.19/4.42            ( r1_xboole_0 @ A @ B ) ) ) & 
% 4.19/4.42       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 4.19/4.42            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 4.19/4.42  thf('13', plain,
% 4.19/4.42      (![X4 : $i, X6 : $i, X7 : $i]:
% 4.19/4.42         (~ (r2_hidden @ X6 @ X4)
% 4.19/4.42          | ~ (r2_hidden @ X6 @ X7)
% 4.19/4.42          | ~ (r1_xboole_0 @ X4 @ X7))),
% 4.19/4.42      inference('cnf', [status(esa)], [t3_xboole_0])).
% 4.19/4.42  thf('14', plain,
% 4.19/4.42      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_2 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 4.19/4.42      inference('sup-', [status(thm)], ['12', '13'])).
% 4.19/4.42  thf('15', plain, (~ (r2_hidden @ sk_D @ (k2_xboole_0 @ sk_B @ sk_B))),
% 4.19/4.42      inference('sup-', [status(thm)], ['11', '14'])).
% 4.19/4.42  thf('16', plain, ((r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_B)),
% 4.19/4.42      inference('sup-', [status(thm)], ['6', '15'])).
% 4.19/4.42  thf(t83_xboole_1, axiom,
% 4.19/4.42    (![A:$i,B:$i]:
% 4.19/4.42     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 4.19/4.42  thf('17', plain,
% 4.19/4.42      (![X26 : $i, X27 : $i]:
% 4.19/4.42         (((k4_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_xboole_0 @ X26 @ X27))),
% 4.19/4.42      inference('cnf', [status(esa)], [t83_xboole_1])).
% 4.19/4.42  thf('18', plain,
% 4.19/4.42      (((k4_xboole_0 @ (k1_tarski @ sk_D) @ sk_B) = (k1_tarski @ sk_D))),
% 4.19/4.42      inference('sup-', [status(thm)], ['16', '17'])).
% 4.19/4.42  thf(t106_xboole_1, axiom,
% 4.19/4.42    (![A:$i,B:$i,C:$i]:
% 4.19/4.42     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 4.19/4.42       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 4.19/4.42  thf('19', plain,
% 4.19/4.42      (![X12 : $i, X13 : $i, X14 : $i]:
% 4.19/4.42         ((r1_xboole_0 @ X12 @ X14)
% 4.19/4.42          | ~ (r1_tarski @ X12 @ (k4_xboole_0 @ X13 @ X14)))),
% 4.19/4.42      inference('cnf', [status(esa)], [t106_xboole_1])).
% 4.19/4.42  thf('20', plain,
% 4.19/4.42      (![X0 : $i]:
% 4.19/4.42         (~ (r1_tarski @ X0 @ (k1_tarski @ sk_D)) | (r1_xboole_0 @ X0 @ sk_B))),
% 4.19/4.42      inference('sup-', [status(thm)], ['18', '19'])).
% 4.19/4.42  thf('21', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_B)),
% 4.19/4.42      inference('sup-', [status(thm)], ['3', '20'])).
% 4.19/4.42  thf(symmetry_r1_xboole_0, axiom,
% 4.19/4.42    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 4.19/4.42  thf('22', plain,
% 4.19/4.42      (![X2 : $i, X3 : $i]:
% 4.19/4.42         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 4.19/4.42      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 4.19/4.42  thf('23', plain, ((r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_A))),
% 4.19/4.42      inference('sup-', [status(thm)], ['21', '22'])).
% 4.19/4.42  thf('24', plain,
% 4.19/4.42      (![X26 : $i, X27 : $i]:
% 4.19/4.42         (((k4_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_xboole_0 @ X26 @ X27))),
% 4.19/4.42      inference('cnf', [status(esa)], [t83_xboole_1])).
% 4.19/4.42  thf('25', plain,
% 4.19/4.42      (((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 4.19/4.42      inference('sup-', [status(thm)], ['23', '24'])).
% 4.19/4.42  thf(t48_xboole_1, axiom,
% 4.19/4.42    (![A:$i,B:$i]:
% 4.19/4.42     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.19/4.42  thf('26', plain,
% 4.19/4.42      (![X15 : $i, X16 : $i]:
% 4.19/4.42         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 4.19/4.42           = (k3_xboole_0 @ X15 @ X16))),
% 4.19/4.42      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.19/4.42  thf('27', plain,
% 4.19/4.42      (![X15 : $i, X16 : $i]:
% 4.19/4.42         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 4.19/4.42           = (k3_xboole_0 @ X15 @ X16))),
% 4.19/4.42      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.19/4.42  thf('28', plain,
% 4.19/4.42      (![X0 : $i, X1 : $i]:
% 4.19/4.42         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 4.19/4.42           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.19/4.42      inference('sup+', [status(thm)], ['26', '27'])).
% 4.19/4.42  thf('29', plain,
% 4.19/4.42      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 4.19/4.42      inference('demod', [status(thm)], ['25', '28'])).
% 4.19/4.42  thf('30', plain,
% 4.19/4.42      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.19/4.42      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.19/4.42  thf(t79_xboole_1, axiom,
% 4.19/4.42    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 4.19/4.42  thf('31', plain,
% 4.19/4.42      (![X24 : $i, X25 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X24 @ X25) @ X25)),
% 4.19/4.42      inference('cnf', [status(esa)], [t79_xboole_1])).
% 4.19/4.42  thf('32', plain,
% 4.19/4.42      (![X2 : $i, X3 : $i]:
% 4.19/4.42         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 4.19/4.42      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 4.19/4.42  thf('33', plain,
% 4.19/4.42      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 4.19/4.42      inference('sup-', [status(thm)], ['31', '32'])).
% 4.19/4.42  thf(t74_xboole_1, axiom,
% 4.19/4.42    (![A:$i,B:$i,C:$i]:
% 4.19/4.42     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 4.19/4.42          ( r1_xboole_0 @ A @ B ) ) ))).
% 4.19/4.42  thf('34', plain,
% 4.19/4.42      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.19/4.42         (~ (r1_xboole_0 @ X21 @ X22)
% 4.19/4.42          | (r1_xboole_0 @ X21 @ (k3_xboole_0 @ X22 @ X23)))),
% 4.19/4.42      inference('cnf', [status(esa)], [t74_xboole_1])).
% 4.19/4.42  thf('35', plain,
% 4.19/4.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.19/4.42         (r1_xboole_0 @ X0 @ (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))),
% 4.19/4.42      inference('sup-', [status(thm)], ['33', '34'])).
% 4.19/4.42  thf('36', plain,
% 4.19/4.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.19/4.42         (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.19/4.42      inference('sup+', [status(thm)], ['30', '35'])).
% 4.19/4.42  thf('37', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 4.19/4.42      inference('sup+', [status(thm)], ['29', '36'])).
% 4.19/4.42  thf('38', plain,
% 4.19/4.42      (![X26 : $i, X27 : $i]:
% 4.19/4.42         (((k4_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_xboole_0 @ X26 @ X27))),
% 4.19/4.42      inference('cnf', [status(esa)], [t83_xboole_1])).
% 4.19/4.42  thf('39', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 4.19/4.42      inference('sup-', [status(thm)], ['37', '38'])).
% 4.19/4.42  thf('40', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('41', plain,
% 4.19/4.42      (![X2 : $i, X3 : $i]:
% 4.19/4.42         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 4.19/4.42      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 4.19/4.42  thf('42', plain, ((r1_xboole_0 @ sk_B @ sk_C_2)),
% 4.19/4.42      inference('sup-', [status(thm)], ['40', '41'])).
% 4.19/4.42  thf('43', plain,
% 4.19/4.42      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 4.19/4.42      inference('sup-', [status(thm)], ['31', '32'])).
% 4.19/4.42  thf('44', plain,
% 4.19/4.42      (![X17 : $i, X18 : $i, X19 : $i]:
% 4.19/4.42         ((r1_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19))
% 4.19/4.42          | ~ (r1_xboole_0 @ X17 @ X18)
% 4.19/4.42          | ~ (r1_xboole_0 @ X17 @ X19))),
% 4.19/4.42      inference('cnf', [status(esa)], [t70_xboole_1])).
% 4.19/4.42  thf('45', plain,
% 4.19/4.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.19/4.42         (~ (r1_xboole_0 @ X0 @ X2)
% 4.19/4.42          | (r1_xboole_0 @ X0 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 4.19/4.42      inference('sup-', [status(thm)], ['43', '44'])).
% 4.19/4.42  thf('46', plain,
% 4.19/4.42      (![X0 : $i]:
% 4.19/4.42         (r1_xboole_0 @ sk_B @ 
% 4.19/4.42          (k2_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_C_2))),
% 4.19/4.42      inference('sup-', [status(thm)], ['42', '45'])).
% 4.19/4.42  thf('47', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_2))),
% 4.19/4.42      inference('sup+', [status(thm)], ['39', '46'])).
% 4.19/4.42  thf('48', plain,
% 4.19/4.42      (![X2 : $i, X3 : $i]:
% 4.19/4.42         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 4.19/4.42      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 4.19/4.42  thf('49', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 4.19/4.42      inference('sup-', [status(thm)], ['47', '48'])).
% 4.19/4.42  thf('50', plain, ($false), inference('demod', [status(thm)], ['0', '49'])).
% 4.19/4.42  
% 4.19/4.42  % SZS output end Refutation
% 4.19/4.42  
% 4.19/4.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
