%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KQwEvWxvH0

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:34 EST 2020

% Result     : Theorem 1.91s
% Output     : Refutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 105 expanded)
%              Number of leaves         :   17 (  40 expanded)
%              Depth                    :   23
%              Number of atoms          :  586 ( 854 expanded)
%              Number of equality atoms :   22 (  40 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t81_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('16',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('21',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t80_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_xboole_0 @ X23 @ X24 )
      | ( r1_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t80_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_xboole_0 @ X23 @ X24 )
      | ( r1_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t80_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ X1 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ X1 ) @ ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['20','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ X1 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['19','32'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('34',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t77_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t77_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ X3 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
      | ~ ( r1_tarski @ X3 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ X1 ) @ sk_B )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X1 ) @ ( k4_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['18','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_C ) @ sk_B ) ),
    inference('sup+',[status(thm)],['15','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ X0 ) @ sk_B ) ),
    inference('sup+',[status(thm)],['14','39'])).

thf('41',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_xboole_0 @ X23 @ X24 )
      | ( r1_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t80_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ X0 ) @ ( k4_xboole_0 @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t77_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X1 ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ X1 ) @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','46'])).

thf('48',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','49'])).

thf('51',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t77_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['1','52'])).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('55',plain,(
    r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['0','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KQwEvWxvH0
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:54:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.91/2.08  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.91/2.08  % Solved by: fo/fo7.sh
% 1.91/2.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.91/2.08  % done 1486 iterations in 1.631s
% 1.91/2.08  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.91/2.08  % SZS output start Refutation
% 1.91/2.08  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.91/2.08  thf(sk_A_type, type, sk_A: $i).
% 1.91/2.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.91/2.08  thf(sk_B_type, type, sk_B: $i).
% 1.91/2.08  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.91/2.08  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.91/2.08  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.91/2.08  thf(sk_C_type, type, sk_C: $i).
% 1.91/2.08  thf(t81_xboole_1, conjecture,
% 1.91/2.08    (![A:$i,B:$i,C:$i]:
% 1.91/2.08     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.91/2.08       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 1.91/2.08  thf(zf_stmt_0, negated_conjecture,
% 1.91/2.08    (~( ![A:$i,B:$i,C:$i]:
% 1.91/2.08        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.91/2.08          ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )),
% 1.91/2.08    inference('cnf.neg', [status(esa)], [t81_xboole_1])).
% 1.91/2.08  thf('0', plain, (~ (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 1.91/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.08  thf(t36_xboole_1, axiom,
% 1.91/2.08    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.91/2.08  thf('1', plain,
% 1.91/2.08      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 1.91/2.08      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.91/2.08  thf(t48_xboole_1, axiom,
% 1.91/2.08    (![A:$i,B:$i]:
% 1.91/2.08     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.91/2.08  thf('2', plain,
% 1.91/2.08      (![X9 : $i, X10 : $i]:
% 1.91/2.08         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 1.91/2.08           = (k3_xboole_0 @ X9 @ X10))),
% 1.91/2.08      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.91/2.08  thf('3', plain,
% 1.91/2.08      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 1.91/2.08      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.91/2.08  thf(t41_xboole_1, axiom,
% 1.91/2.08    (![A:$i,B:$i,C:$i]:
% 1.91/2.08     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.91/2.08       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.91/2.08  thf('4', plain,
% 1.91/2.08      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.91/2.08         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 1.91/2.08           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 1.91/2.08      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.91/2.08  thf('5', plain,
% 1.91/2.08      (![X9 : $i, X10 : $i]:
% 1.91/2.08         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 1.91/2.08           = (k3_xboole_0 @ X9 @ X10))),
% 1.91/2.08      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.91/2.08  thf('6', plain,
% 1.91/2.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.08         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ 
% 1.91/2.08           (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 1.91/2.08           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 1.91/2.08      inference('sup+', [status(thm)], ['4', '5'])).
% 1.91/2.08  thf('7', plain,
% 1.91/2.08      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.91/2.08         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 1.91/2.08           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 1.91/2.08      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.91/2.08  thf('8', plain,
% 1.91/2.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.08         ((k4_xboole_0 @ X2 @ 
% 1.91/2.08           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 1.91/2.08           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 1.91/2.08      inference('demod', [status(thm)], ['6', '7'])).
% 1.91/2.08  thf(commutativity_k2_xboole_0, axiom,
% 1.91/2.08    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.91/2.08  thf('9', plain,
% 1.91/2.08      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.91/2.08      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.91/2.08  thf('10', plain,
% 1.91/2.08      (![X9 : $i, X10 : $i]:
% 1.91/2.08         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 1.91/2.08           = (k3_xboole_0 @ X9 @ X10))),
% 1.91/2.08      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.91/2.08  thf('11', plain,
% 1.91/2.08      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.91/2.08         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 1.91/2.08           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 1.91/2.08      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.91/2.08  thf('12', plain,
% 1.91/2.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.08         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.91/2.08           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 1.91/2.08      inference('sup+', [status(thm)], ['10', '11'])).
% 1.91/2.08  thf('13', plain,
% 1.91/2.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.08         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.91/2.08           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.91/2.08      inference('sup+', [status(thm)], ['9', '12'])).
% 1.91/2.08  thf('14', plain,
% 1.91/2.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.08         ((k4_xboole_0 @ (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1)
% 1.91/2.08           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 1.91/2.08      inference('demod', [status(thm)], ['8', '13'])).
% 1.91/2.08  thf('15', plain,
% 1.91/2.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.08         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.91/2.08           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.91/2.08      inference('sup+', [status(thm)], ['9', '12'])).
% 1.91/2.08  thf('16', plain,
% 1.91/2.08      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.91/2.08         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 1.91/2.08           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 1.91/2.08      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.91/2.08  thf('17', plain,
% 1.91/2.08      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 1.91/2.08      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.91/2.08  thf('18', plain,
% 1.91/2.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.08         (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 1.91/2.08          (k4_xboole_0 @ X2 @ X1))),
% 1.91/2.08      inference('sup+', [status(thm)], ['16', '17'])).
% 1.91/2.08  thf('19', plain,
% 1.91/2.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.08         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.91/2.08           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 1.91/2.08      inference('sup+', [status(thm)], ['10', '11'])).
% 1.91/2.08  thf('20', plain,
% 1.91/2.08      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.91/2.08      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.91/2.08  thf('21', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 1.91/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.08  thf(symmetry_r1_xboole_0, axiom,
% 1.91/2.08    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.91/2.08  thf('22', plain,
% 1.91/2.08      (![X2 : $i, X3 : $i]:
% 1.91/2.08         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.91/2.08      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.91/2.08  thf('23', plain, ((r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 1.91/2.08      inference('sup-', [status(thm)], ['21', '22'])).
% 1.91/2.08  thf(t80_xboole_1, axiom,
% 1.91/2.08    (![A:$i,B:$i,C:$i]:
% 1.91/2.08     ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 1.91/2.08  thf('24', plain,
% 1.91/2.08      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.91/2.08         (~ (r1_xboole_0 @ X23 @ X24)
% 1.91/2.08          | (r1_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X25)))),
% 1.91/2.08      inference('cnf', [status(esa)], [t80_xboole_1])).
% 1.91/2.08  thf('25', plain,
% 1.91/2.08      (![X0 : $i]:
% 1.91/2.08         (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ (k4_xboole_0 @ sk_A @ X0))),
% 1.91/2.08      inference('sup-', [status(thm)], ['23', '24'])).
% 1.91/2.08  thf('26', plain,
% 1.91/2.08      (![X2 : $i, X3 : $i]:
% 1.91/2.08         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.91/2.08      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.91/2.08  thf('27', plain,
% 1.91/2.08      (![X0 : $i]:
% 1.91/2.08         (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ (k4_xboole_0 @ sk_B @ sk_C))),
% 1.91/2.08      inference('sup-', [status(thm)], ['25', '26'])).
% 1.91/2.08  thf('28', plain,
% 1.91/2.08      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.91/2.08         (~ (r1_xboole_0 @ X23 @ X24)
% 1.91/2.08          | (r1_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X25)))),
% 1.91/2.08      inference('cnf', [status(esa)], [t80_xboole_1])).
% 1.91/2.08  thf('29', plain,
% 1.91/2.08      (![X0 : $i, X1 : $i]:
% 1.91/2.08         (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ 
% 1.91/2.08          (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X1))),
% 1.91/2.08      inference('sup-', [status(thm)], ['27', '28'])).
% 1.91/2.08  thf('30', plain,
% 1.91/2.08      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.91/2.08         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 1.91/2.08           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 1.91/2.08      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.91/2.08  thf('31', plain,
% 1.91/2.08      (![X0 : $i, X1 : $i]:
% 1.91/2.08         (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ 
% 1.91/2.08          (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ X1)))),
% 1.91/2.08      inference('demod', [status(thm)], ['29', '30'])).
% 1.91/2.08  thf('32', plain,
% 1.91/2.08      (![X0 : $i, X1 : $i]:
% 1.91/2.08         (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ X1) @ 
% 1.91/2.08          (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ sk_C)))),
% 1.91/2.08      inference('sup+', [status(thm)], ['20', '31'])).
% 1.91/2.08  thf('33', plain,
% 1.91/2.08      (![X0 : $i, X1 : $i]:
% 1.91/2.08         (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ X1) @ 
% 1.91/2.08          (k4_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ sk_C))),
% 1.91/2.08      inference('sup+', [status(thm)], ['19', '32'])).
% 1.91/2.08  thf(t49_xboole_1, axiom,
% 1.91/2.08    (![A:$i,B:$i,C:$i]:
% 1.91/2.08     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.91/2.08       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 1.91/2.08  thf('34', plain,
% 1.91/2.08      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.91/2.08         ((k3_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 1.91/2.08           = (k4_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13))),
% 1.91/2.08      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.91/2.08  thf(t77_xboole_1, axiom,
% 1.91/2.08    (![A:$i,B:$i,C:$i]:
% 1.91/2.08     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 1.91/2.08          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 1.91/2.08  thf('35', plain,
% 1.91/2.08      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.91/2.08         ((r1_xboole_0 @ X18 @ X19)
% 1.91/2.08          | ~ (r1_xboole_0 @ X18 @ (k3_xboole_0 @ X19 @ X20))
% 1.91/2.08          | ~ (r1_tarski @ X18 @ X20))),
% 1.91/2.08      inference('cnf', [status(esa)], [t77_xboole_1])).
% 1.91/2.08  thf('36', plain,
% 1.91/2.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.91/2.08         (~ (r1_xboole_0 @ X3 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 1.91/2.08          | ~ (r1_tarski @ X3 @ (k4_xboole_0 @ X1 @ X0))
% 1.91/2.08          | (r1_xboole_0 @ X3 @ X2))),
% 1.91/2.08      inference('sup-', [status(thm)], ['34', '35'])).
% 1.91/2.08  thf('37', plain,
% 1.91/2.08      (![X0 : $i, X1 : $i]:
% 1.91/2.08         ((r1_xboole_0 @ (k4_xboole_0 @ sk_A @ X1) @ sk_B)
% 1.91/2.08          | ~ (r1_tarski @ (k4_xboole_0 @ sk_A @ X1) @ 
% 1.91/2.08               (k4_xboole_0 @ X0 @ sk_C)))),
% 1.91/2.08      inference('sup-', [status(thm)], ['33', '36'])).
% 1.91/2.08  thf('38', plain,
% 1.91/2.08      (![X0 : $i]:
% 1.91/2.08         (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ X0)) @ sk_B)),
% 1.91/2.08      inference('sup-', [status(thm)], ['18', '37'])).
% 1.91/2.08  thf('39', plain,
% 1.91/2.08      (![X0 : $i]:
% 1.91/2.08         (r1_xboole_0 @ (k4_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_C) @ sk_B)),
% 1.91/2.08      inference('sup+', [status(thm)], ['15', '38'])).
% 1.91/2.08  thf('40', plain,
% 1.91/2.08      (![X0 : $i]:
% 1.91/2.08         (r1_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ X0) @ sk_B)),
% 1.91/2.08      inference('sup+', [status(thm)], ['14', '39'])).
% 1.91/2.08  thf('41', plain,
% 1.91/2.08      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.91/2.08         (~ (r1_xboole_0 @ X23 @ X24)
% 1.91/2.08          | (r1_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X25)))),
% 1.91/2.08      inference('cnf', [status(esa)], [t80_xboole_1])).
% 1.91/2.08  thf('42', plain,
% 1.91/2.08      (![X0 : $i, X1 : $i]:
% 1.91/2.08         (r1_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ X0) @ 
% 1.91/2.08          (k4_xboole_0 @ sk_B @ X1))),
% 1.91/2.08      inference('sup-', [status(thm)], ['40', '41'])).
% 1.91/2.08  thf('43', plain,
% 1.91/2.08      (![X2 : $i, X3 : $i]:
% 1.91/2.08         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.91/2.08      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.91/2.08  thf('44', plain,
% 1.91/2.08      (![X0 : $i, X1 : $i]:
% 1.91/2.08         (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 1.91/2.08          (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ X1))),
% 1.91/2.08      inference('sup-', [status(thm)], ['42', '43'])).
% 1.91/2.08  thf('45', plain,
% 1.91/2.08      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.91/2.08         ((r1_xboole_0 @ X18 @ X19)
% 1.91/2.08          | ~ (r1_xboole_0 @ X18 @ (k3_xboole_0 @ X19 @ X20))
% 1.91/2.08          | ~ (r1_tarski @ X18 @ X20))),
% 1.91/2.08      inference('cnf', [status(esa)], [t77_xboole_1])).
% 1.91/2.08  thf('46', plain,
% 1.91/2.08      (![X0 : $i, X1 : $i]:
% 1.91/2.08         (~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X1) @ X0)
% 1.91/2.08          | (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ X1) @ 
% 1.91/2.08             (k4_xboole_0 @ sk_A @ sk_C)))),
% 1.91/2.08      inference('sup-', [status(thm)], ['44', '45'])).
% 1.91/2.08  thf('47', plain,
% 1.91/2.08      (![X0 : $i]:
% 1.91/2.08         (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ (k4_xboole_0 @ sk_A @ sk_C))),
% 1.91/2.08      inference('sup-', [status(thm)], ['3', '46'])).
% 1.91/2.08  thf('48', plain,
% 1.91/2.08      (![X2 : $i, X3 : $i]:
% 1.91/2.08         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.91/2.08      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.91/2.08  thf('49', plain,
% 1.91/2.08      (![X0 : $i]:
% 1.91/2.08         (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ (k4_xboole_0 @ sk_B @ X0))),
% 1.91/2.08      inference('sup-', [status(thm)], ['47', '48'])).
% 1.91/2.08  thf('50', plain,
% 1.91/2.08      (![X0 : $i]:
% 1.91/2.08         (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ (k3_xboole_0 @ sk_B @ X0))),
% 1.91/2.08      inference('sup+', [status(thm)], ['2', '49'])).
% 1.91/2.08  thf('51', plain,
% 1.91/2.08      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.91/2.08         ((r1_xboole_0 @ X18 @ X19)
% 1.91/2.08          | ~ (r1_xboole_0 @ X18 @ (k3_xboole_0 @ X19 @ X20))
% 1.91/2.08          | ~ (r1_tarski @ X18 @ X20))),
% 1.91/2.08      inference('cnf', [status(esa)], [t77_xboole_1])).
% 1.91/2.08  thf('52', plain,
% 1.91/2.08      (![X0 : $i]:
% 1.91/2.08         (~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C) @ X0)
% 1.91/2.08          | (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B))),
% 1.91/2.08      inference('sup-', [status(thm)], ['50', '51'])).
% 1.91/2.08  thf('53', plain, ((r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 1.91/2.08      inference('sup-', [status(thm)], ['1', '52'])).
% 1.91/2.08  thf('54', plain,
% 1.91/2.08      (![X2 : $i, X3 : $i]:
% 1.91/2.08         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.91/2.08      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.91/2.08  thf('55', plain, ((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 1.91/2.08      inference('sup-', [status(thm)], ['53', '54'])).
% 1.91/2.08  thf('56', plain, ($false), inference('demod', [status(thm)], ['0', '55'])).
% 1.91/2.08  
% 1.91/2.08  % SZS output end Refutation
% 1.91/2.08  
% 1.94/2.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
