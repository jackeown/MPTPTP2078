%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xr1S4cVU82

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:36 EST 2020

% Result     : Theorem 0.72s
% Output     : Refutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 133 expanded)
%              Number of leaves         :   24 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :  622 ( 997 expanded)
%              Number of equality atoms :   62 ( 111 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    ~ ( r1_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('2',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('7',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X24 @ X25 ) @ ( k3_xboole_0 @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

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
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9','12'])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['1','13'])).

thf(t50_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('15',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t50_xboole_1])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('17',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ ( k3_xboole_0 @ X19 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
    = ( k4_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['14','21'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('24',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('26',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('31',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X24 @ X25 ) @ ( k3_xboole_0 @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('37',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('38',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('44',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X24 @ X25 ) @ ( k3_xboole_0 @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','45','46','47','48'])).

thf('50',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','51'])).

thf('53',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['22','52'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('54',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X27 @ X28 ) @ X28 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('55',plain,(
    r1_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['0','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xr1S4cVU82
% 0.13/0.37  % Computer   : n021.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 13:12:19 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.72/0.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.72/0.90  % Solved by: fo/fo7.sh
% 0.72/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.72/0.90  % done 572 iterations in 0.413s
% 0.72/0.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.72/0.90  % SZS output start Refutation
% 0.72/0.90  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.72/0.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.72/0.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.72/0.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.72/0.90  thf(sk_B_type, type, sk_B: $i > $i).
% 0.72/0.90  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.72/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.72/0.90  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.72/0.90  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.72/0.90  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.72/0.90  thf(t81_xboole_1, conjecture,
% 0.72/0.90    (![A:$i,B:$i,C:$i]:
% 0.72/0.90     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.72/0.90       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.72/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.72/0.90    (~( ![A:$i,B:$i,C:$i]:
% 0.72/0.90        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.72/0.90          ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )),
% 0.72/0.90    inference('cnf.neg', [status(esa)], [t81_xboole_1])).
% 0.72/0.90  thf('0', plain, (~ (r1_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf(t48_xboole_1, axiom,
% 0.72/0.90    (![A:$i,B:$i]:
% 0.72/0.90     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.72/0.90  thf('1', plain,
% 0.72/0.90      (![X14 : $i, X15 : $i]:
% 0.72/0.90         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.72/0.90           = (k3_xboole_0 @ X14 @ X15))),
% 0.72/0.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.72/0.90  thf('2', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf(t7_xboole_0, axiom,
% 0.72/0.90    (![A:$i]:
% 0.72/0.90     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.72/0.90          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.72/0.90  thf('3', plain,
% 0.72/0.90      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.72/0.90      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.72/0.90  thf(t4_xboole_0, axiom,
% 0.72/0.90    (![A:$i,B:$i]:
% 0.72/0.90     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.72/0.90            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.72/0.90       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.72/0.90            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.72/0.90  thf('4', plain,
% 0.72/0.90      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.72/0.90         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.72/0.90          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.72/0.90      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.72/0.90  thf('5', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.72/0.90      inference('sup-', [status(thm)], ['3', '4'])).
% 0.72/0.90  thf('6', plain,
% 0.72/0.90      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1)) = (k1_xboole_0))),
% 0.72/0.90      inference('sup-', [status(thm)], ['2', '5'])).
% 0.72/0.90  thf(t52_xboole_1, axiom,
% 0.72/0.90    (![A:$i,B:$i,C:$i]:
% 0.72/0.90     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.72/0.90       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.72/0.90  thf('7', plain,
% 0.72/0.90      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.72/0.90         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X26))
% 0.72/0.90           = (k2_xboole_0 @ (k4_xboole_0 @ X24 @ X25) @ 
% 0.72/0.90              (k3_xboole_0 @ X24 @ X26)))),
% 0.72/0.90      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.72/0.90  thf('8', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         ((k4_xboole_0 @ sk_A @ 
% 0.72/0.90           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1)))
% 0.72/0.90           = (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ k1_xboole_0))),
% 0.72/0.90      inference('sup+', [status(thm)], ['6', '7'])).
% 0.72/0.90  thf(commutativity_k2_xboole_0, axiom,
% 0.72/0.90    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.72/0.90  thf('9', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.72/0.90      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.72/0.90  thf('10', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.72/0.90      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.72/0.90  thf(t1_boole, axiom,
% 0.72/0.90    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.72/0.90  thf('11', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.72/0.90      inference('cnf', [status(esa)], [t1_boole])).
% 0.72/0.90  thf('12', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.72/0.90      inference('sup+', [status(thm)], ['10', '11'])).
% 0.72/0.90  thf('13', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         ((k4_xboole_0 @ sk_A @ 
% 0.72/0.90           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1)))
% 0.72/0.90           = (k4_xboole_0 @ sk_A @ X0))),
% 0.72/0.90      inference('demod', [status(thm)], ['8', '9', '12'])).
% 0.72/0.90  thf('14', plain,
% 0.72/0.90      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.72/0.90         = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.72/0.90      inference('sup+', [status(thm)], ['1', '13'])).
% 0.72/0.90  thf(t50_xboole_1, axiom,
% 0.72/0.90    (![A:$i,B:$i,C:$i]:
% 0.72/0.90     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.72/0.90       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.72/0.90  thf('15', plain,
% 0.72/0.90      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.72/0.90         ((k3_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 0.72/0.90           = (k4_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ 
% 0.72/0.90              (k3_xboole_0 @ X19 @ X21)))),
% 0.72/0.90      inference('cnf', [status(esa)], [t50_xboole_1])).
% 0.72/0.90  thf(t49_xboole_1, axiom,
% 0.72/0.90    (![A:$i,B:$i,C:$i]:
% 0.72/0.90     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.72/0.90       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.72/0.90  thf('16', plain,
% 0.72/0.90      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.72/0.90         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.72/0.90           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 0.72/0.90      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.72/0.90  thf('17', plain,
% 0.72/0.90      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.72/0.90         ((k3_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 0.72/0.90           = (k3_xboole_0 @ X19 @ 
% 0.72/0.90              (k4_xboole_0 @ X20 @ (k3_xboole_0 @ X19 @ X21))))),
% 0.72/0.90      inference('demod', [status(thm)], ['15', '16'])).
% 0.72/0.90  thf(t47_xboole_1, axiom,
% 0.72/0.90    (![A:$i,B:$i]:
% 0.72/0.90     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.72/0.90  thf('18', plain,
% 0.72/0.90      (![X12 : $i, X13 : $i]:
% 0.72/0.90         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 0.72/0.90           = (k4_xboole_0 @ X12 @ X13))),
% 0.72/0.90      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.72/0.90  thf('19', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.90         ((k4_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 0.72/0.90           = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0))))),
% 0.72/0.90      inference('sup+', [status(thm)], ['17', '18'])).
% 0.72/0.90  thf('20', plain,
% 0.72/0.90      (![X12 : $i, X13 : $i]:
% 0.72/0.90         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 0.72/0.90           = (k4_xboole_0 @ X12 @ X13))),
% 0.72/0.90      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.72/0.90  thf('21', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.90         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.72/0.90           = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0))))),
% 0.72/0.90      inference('demod', [status(thm)], ['19', '20'])).
% 0.72/0.90  thf('22', plain,
% 0.72/0.90      (((k4_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_A @ sk_C_1))
% 0.72/0.90         = (k4_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_A @ sk_B_1)))),
% 0.72/0.90      inference('sup+', [status(thm)], ['14', '21'])).
% 0.72/0.90  thf(t3_boole, axiom,
% 0.72/0.90    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.72/0.90  thf('23', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.72/0.90      inference('cnf', [status(esa)], [t3_boole])).
% 0.72/0.90  thf('24', plain,
% 0.72/0.90      (![X14 : $i, X15 : $i]:
% 0.72/0.90         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.72/0.90           = (k3_xboole_0 @ X14 @ X15))),
% 0.72/0.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.72/0.90  thf('25', plain,
% 0.72/0.90      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.72/0.90      inference('sup+', [status(thm)], ['23', '24'])).
% 0.72/0.90  thf(t2_boole, axiom,
% 0.72/0.90    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.72/0.90  thf('26', plain,
% 0.72/0.90      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.72/0.90      inference('cnf', [status(esa)], [t2_boole])).
% 0.72/0.90  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.72/0.90      inference('demod', [status(thm)], ['25', '26'])).
% 0.72/0.90  thf('28', plain,
% 0.72/0.90      (![X14 : $i, X15 : $i]:
% 0.72/0.90         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.72/0.90           = (k3_xboole_0 @ X14 @ X15))),
% 0.72/0.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.72/0.90  thf('29', plain,
% 0.72/0.90      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.72/0.90      inference('sup+', [status(thm)], ['27', '28'])).
% 0.72/0.90  thf('30', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.72/0.90      inference('cnf', [status(esa)], [t3_boole])).
% 0.72/0.90  thf('31', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.72/0.90      inference('demod', [status(thm)], ['29', '30'])).
% 0.72/0.90  thf('32', plain,
% 0.72/0.90      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.72/0.90         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X26))
% 0.72/0.90           = (k2_xboole_0 @ (k4_xboole_0 @ X24 @ X25) @ 
% 0.72/0.90              (k3_xboole_0 @ X24 @ X26)))),
% 0.72/0.90      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.72/0.90  thf('33', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.72/0.90      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.72/0.90  thf('34', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.90         ((k2_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X2 @ X1))
% 0.72/0.90           = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.72/0.90      inference('sup+', [status(thm)], ['32', '33'])).
% 0.72/0.90  thf('35', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.72/0.90           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.72/0.90      inference('sup+', [status(thm)], ['31', '34'])).
% 0.72/0.90  thf('36', plain,
% 0.72/0.90      (![X14 : $i, X15 : $i]:
% 0.72/0.90         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.72/0.90           = (k3_xboole_0 @ X14 @ X15))),
% 0.72/0.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.72/0.90  thf('37', plain,
% 0.72/0.90      (![X12 : $i, X13 : $i]:
% 0.72/0.90         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 0.72/0.90           = (k4_xboole_0 @ X12 @ X13))),
% 0.72/0.90      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.72/0.90  thf(t39_xboole_1, axiom,
% 0.72/0.90    (![A:$i,B:$i]:
% 0.72/0.90     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.72/0.90  thf('38', plain,
% 0.72/0.90      (![X9 : $i, X10 : $i]:
% 0.72/0.90         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.72/0.90           = (k2_xboole_0 @ X9 @ X10))),
% 0.72/0.90      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.72/0.90  thf('39', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.72/0.90           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.72/0.90      inference('sup+', [status(thm)], ['37', '38'])).
% 0.72/0.90  thf('40', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.72/0.90      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.72/0.90  thf('41', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.72/0.90           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.72/0.90      inference('demod', [status(thm)], ['39', '40'])).
% 0.72/0.90  thf('42', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 0.72/0.90           (k3_xboole_0 @ X1 @ X0))
% 0.72/0.90           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.72/0.90      inference('sup+', [status(thm)], ['36', '41'])).
% 0.72/0.90  thf('43', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.72/0.90      inference('demod', [status(thm)], ['29', '30'])).
% 0.72/0.90  thf('44', plain,
% 0.72/0.90      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.72/0.90         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.72/0.90           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 0.72/0.90      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.72/0.90  thf('45', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.72/0.90           = (k4_xboole_0 @ X0 @ X1))),
% 0.72/0.90      inference('sup+', [status(thm)], ['43', '44'])).
% 0.72/0.90  thf('46', plain,
% 0.72/0.90      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.72/0.90         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X26))
% 0.72/0.90           = (k2_xboole_0 @ (k4_xboole_0 @ X24 @ X25) @ 
% 0.72/0.90              (k3_xboole_0 @ X24 @ X26)))),
% 0.72/0.90      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.72/0.90  thf('47', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.72/0.90      inference('demod', [status(thm)], ['25', '26'])).
% 0.72/0.90  thf('48', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.72/0.90           = (k4_xboole_0 @ X0 @ X1))),
% 0.72/0.90      inference('sup+', [status(thm)], ['43', '44'])).
% 0.72/0.90  thf('49', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 0.72/0.90           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.72/0.90      inference('demod', [status(thm)], ['42', '45', '46', '47', '48'])).
% 0.72/0.90  thf('50', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.72/0.90      inference('cnf', [status(esa)], [t3_boole])).
% 0.72/0.90  thf('51', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.72/0.90      inference('demod', [status(thm)], ['49', '50'])).
% 0.72/0.90  thf('52', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.72/0.90      inference('demod', [status(thm)], ['35', '51'])).
% 0.72/0.90  thf('53', plain,
% 0.72/0.90      (((k4_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_A @ sk_C_1)) = (sk_B_1))),
% 0.72/0.90      inference('demod', [status(thm)], ['22', '52'])).
% 0.72/0.90  thf(t79_xboole_1, axiom,
% 0.72/0.90    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.72/0.90  thf('54', plain,
% 0.72/0.90      (![X27 : $i, X28 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X27 @ X28) @ X28)),
% 0.72/0.90      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.72/0.90  thf('55', plain, ((r1_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.72/0.90      inference('sup+', [status(thm)], ['53', '54'])).
% 0.72/0.90  thf('56', plain, ($false), inference('demod', [status(thm)], ['0', '55'])).
% 0.72/0.90  
% 0.72/0.90  % SZS output end Refutation
% 0.72/0.90  
% 0.72/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
