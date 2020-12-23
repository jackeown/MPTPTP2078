%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TSf9CijInl

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:38 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 257 expanded)
%              Number of leaves         :   18 (  87 expanded)
%              Depth                    :   24
%              Number of atoms          :  587 (1911 expanded)
%              Number of equality atoms :    8 (  32 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t106_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_xboole_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('3',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 )
      | ( r1_xboole_0 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','10'])).

thf('12',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('17',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','26'])).

thf(t73_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_tarski @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) )
      | ~ ( r1_xboole_0 @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['17','29'])).

thf('31',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 )
      | ( r1_xboole_0 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('35',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_tarski @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) )
      | ~ ( r1_xboole_0 @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) @ X2 ) ),
    inference('sup+',[status(thm)],['15','37'])).

thf('39',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ X2 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('42',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('47',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 )
      | ( r1_xboole_0 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ X2 ) @ X0 ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('53',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_tarski @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) )
      | ~ ( r1_xboole_0 @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['44','55'])).

thf('57',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 )
      | ( r1_xboole_0 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('65',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('67',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('69',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['11','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TSf9CijInl
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:03:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.47/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.65  % Solved by: fo/fo7.sh
% 0.47/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.65  % done 327 iterations in 0.221s
% 0.47/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.65  % SZS output start Refutation
% 0.47/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.65  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.47/0.65  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.47/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.65  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.47/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.47/0.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.47/0.65  thf(t106_xboole_1, conjecture,
% 0.47/0.65    (![A:$i,B:$i,C:$i]:
% 0.47/0.65     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.47/0.65       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.47/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.65    (~( ![A:$i,B:$i,C:$i]:
% 0.47/0.65        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.47/0.65          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.47/0.65    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.47/0.65  thf('0', plain,
% 0.47/0.65      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('1', plain,
% 0.47/0.65      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.47/0.65      inference('split', [status(esa)], ['0'])).
% 0.47/0.65  thf(t79_xboole_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.47/0.65  thf('2', plain,
% 0.47/0.65      (![X20 : $i, X21 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X21)),
% 0.47/0.65      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.47/0.65  thf('3', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(t63_xboole_1, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i]:
% 0.47/0.65     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.47/0.65       ( r1_xboole_0 @ A @ C ) ))).
% 0.47/0.65  thf('4', plain,
% 0.47/0.65      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.65         (~ (r1_tarski @ X14 @ X15)
% 0.47/0.65          | ~ (r1_xboole_0 @ X15 @ X16)
% 0.47/0.65          | (r1_xboole_0 @ X14 @ X16))),
% 0.47/0.65      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.47/0.65  thf('5', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((r1_xboole_0 @ sk_A @ X0)
% 0.47/0.65          | ~ (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C_1) @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['3', '4'])).
% 0.47/0.65  thf('6', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.47/0.65      inference('sup-', [status(thm)], ['2', '5'])).
% 0.47/0.65  thf('7', plain,
% 0.47/0.65      ((~ (r1_xboole_0 @ sk_A @ sk_C_1)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 0.47/0.65      inference('split', [status(esa)], ['0'])).
% 0.47/0.65  thf('8', plain, (((r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.47/0.65      inference('sup-', [status(thm)], ['6', '7'])).
% 0.47/0.65  thf('9', plain,
% 0.47/0.65      (~ ((r1_tarski @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.47/0.65      inference('split', [status(esa)], ['0'])).
% 0.47/0.65  thf('10', plain, (~ ((r1_tarski @ sk_A @ sk_B))),
% 0.47/0.65      inference('sat_resolution*', [status(thm)], ['8', '9'])).
% 0.47/0.65  thf('11', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.47/0.65      inference('simpl_trail', [status(thm)], ['1', '10'])).
% 0.47/0.65  thf('12', plain,
% 0.47/0.65      (![X20 : $i, X21 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X21)),
% 0.47/0.65      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.47/0.65  thf(symmetry_r1_xboole_0, axiom,
% 0.47/0.65    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.47/0.65  thf('13', plain,
% 0.47/0.65      (![X4 : $i, X5 : $i]:
% 0.47/0.65         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 0.47/0.65      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.47/0.65  thf('14', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['12', '13'])).
% 0.47/0.65  thf(t41_xboole_1, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i]:
% 0.47/0.65     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.47/0.65       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.47/0.65  thf('15', plain,
% 0.47/0.65      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.47/0.65         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.47/0.65           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.47/0.65  thf('16', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['12', '13'])).
% 0.47/0.65  thf('17', plain,
% 0.47/0.65      (![X20 : $i, X21 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X21)),
% 0.47/0.65      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.47/0.65  thf(t39_xboole_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.47/0.65  thf('18', plain,
% 0.47/0.65      (![X6 : $i, X7 : $i]:
% 0.47/0.65         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.47/0.65           = (k2_xboole_0 @ X6 @ X7))),
% 0.47/0.65      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.47/0.65  thf(d3_tarski, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( r1_tarski @ A @ B ) <=>
% 0.47/0.65       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.47/0.65  thf('19', plain,
% 0.47/0.65      (![X1 : $i, X3 : $i]:
% 0.47/0.65         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.65  thf('20', plain,
% 0.47/0.65      (![X1 : $i, X3 : $i]:
% 0.47/0.65         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.65  thf('21', plain,
% 0.47/0.65      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['19', '20'])).
% 0.47/0.65  thf('22', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.47/0.65      inference('simplify', [status(thm)], ['21'])).
% 0.47/0.65  thf(t44_xboole_1, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i]:
% 0.47/0.65     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.47/0.65       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.47/0.65  thf('23', plain,
% 0.47/0.65      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.65         ((r1_tarski @ X11 @ (k2_xboole_0 @ X12 @ X13))
% 0.47/0.65          | ~ (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X13))),
% 0.47/0.65      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.47/0.65  thf('24', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['22', '23'])).
% 0.47/0.65  thf('25', plain,
% 0.47/0.65      (![X6 : $i, X7 : $i]:
% 0.47/0.65         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.47/0.65           = (k2_xboole_0 @ X6 @ X7))),
% 0.47/0.65      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.47/0.65  thf('26', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ X1))),
% 0.47/0.65      inference('demod', [status(thm)], ['24', '25'])).
% 0.47/0.65  thf('27', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 0.47/0.65      inference('sup+', [status(thm)], ['18', '26'])).
% 0.47/0.65  thf(t73_xboole_1, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i]:
% 0.47/0.65     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.47/0.65       ( r1_tarski @ A @ B ) ))).
% 0.47/0.65  thf('28', plain,
% 0.47/0.65      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.47/0.65         ((r1_tarski @ X17 @ X18)
% 0.47/0.65          | ~ (r1_tarski @ X17 @ (k2_xboole_0 @ X18 @ X19))
% 0.47/0.65          | ~ (r1_xboole_0 @ X17 @ X19))),
% 0.47/0.65      inference('cnf', [status(esa)], [t73_xboole_1])).
% 0.47/0.65  thf('29', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (~ (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.47/0.65          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X1))),
% 0.47/0.65      inference('sup-', [status(thm)], ['27', '28'])).
% 0.47/0.65  thf('30', plain, (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X0)),
% 0.47/0.65      inference('sup-', [status(thm)], ['17', '29'])).
% 0.47/0.65  thf('31', plain,
% 0.47/0.65      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.65         (~ (r1_tarski @ X14 @ X15)
% 0.47/0.65          | ~ (r1_xboole_0 @ X15 @ X16)
% 0.47/0.65          | (r1_xboole_0 @ X14 @ X16))),
% 0.47/0.65      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.47/0.65  thf('32', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         ((r1_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.47/0.65          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.47/0.65      inference('sup-', [status(thm)], ['30', '31'])).
% 0.47/0.65  thf('33', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ (k4_xboole_0 @ X1 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['16', '32'])).
% 0.47/0.65  thf('34', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ X1))),
% 0.47/0.65      inference('demod', [status(thm)], ['24', '25'])).
% 0.47/0.65  thf('35', plain,
% 0.47/0.65      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.47/0.65         ((r1_tarski @ X17 @ X18)
% 0.47/0.65          | ~ (r1_tarski @ X17 @ (k2_xboole_0 @ X18 @ X19))
% 0.47/0.65          | ~ (r1_xboole_0 @ X17 @ X19))),
% 0.47/0.65      inference('cnf', [status(esa)], [t73_xboole_1])).
% 0.47/0.65  thf('36', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | (r1_tarski @ X0 @ X1))),
% 0.47/0.65      inference('sup-', [status(thm)], ['34', '35'])).
% 0.47/0.65  thf('37', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 0.47/0.65      inference('sup-', [status(thm)], ['33', '36'])).
% 0.47/0.65  thf('38', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.65         (r1_tarski @ 
% 0.47/0.65          (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))) @ 
% 0.47/0.65          X2)),
% 0.47/0.65      inference('sup+', [status(thm)], ['15', '37'])).
% 0.47/0.65  thf('39', plain,
% 0.47/0.65      (![X6 : $i, X7 : $i]:
% 0.47/0.65         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.47/0.65           = (k2_xboole_0 @ X6 @ X7))),
% 0.47/0.65      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.47/0.65  thf('40', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.65         (r1_tarski @ (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) @ X2)),
% 0.47/0.65      inference('demod', [status(thm)], ['38', '39'])).
% 0.47/0.65  thf('41', plain,
% 0.47/0.65      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.47/0.65         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.47/0.65           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.47/0.65  thf('42', plain,
% 0.47/0.65      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.65         ((r1_tarski @ X11 @ (k2_xboole_0 @ X12 @ X13))
% 0.47/0.65          | ~ (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X13))),
% 0.47/0.65      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.47/0.65  thf('43', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.65         (~ (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 0.47/0.65          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ (k2_xboole_0 @ X0 @ X3)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['41', '42'])).
% 0.47/0.65  thf('44', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.65         (r1_tarski @ (k4_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['40', '43'])).
% 0.47/0.65  thf('45', plain,
% 0.47/0.65      (![X20 : $i, X21 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X21)),
% 0.47/0.65      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.47/0.65  thf('46', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 0.47/0.65      inference('sup-', [status(thm)], ['33', '36'])).
% 0.47/0.65  thf('47', plain,
% 0.47/0.65      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.65         (~ (r1_tarski @ X14 @ X15)
% 0.47/0.65          | ~ (r1_xboole_0 @ X15 @ X16)
% 0.47/0.65          | (r1_xboole_0 @ X14 @ X16))),
% 0.47/0.65      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.47/0.65  thf('48', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.65         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X2)
% 0.47/0.65          | ~ (r1_xboole_0 @ X0 @ X2))),
% 0.47/0.65      inference('sup-', [status(thm)], ['46', '47'])).
% 0.47/0.65  thf('49', plain,
% 0.47/0.65      (![X0 : $i, X2 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X2 @ X2) @ X0)),
% 0.47/0.65      inference('sup-', [status(thm)], ['45', '48'])).
% 0.47/0.65  thf('50', plain,
% 0.47/0.65      (![X4 : $i, X5 : $i]:
% 0.47/0.65         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 0.47/0.65      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.47/0.65  thf('51', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X1))),
% 0.47/0.65      inference('sup-', [status(thm)], ['49', '50'])).
% 0.47/0.65  thf('52', plain,
% 0.47/0.65      (![X6 : $i, X7 : $i]:
% 0.47/0.65         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.47/0.65           = (k2_xboole_0 @ X6 @ X7))),
% 0.47/0.65      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.47/0.65  thf('53', plain,
% 0.47/0.65      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.47/0.65         ((r1_tarski @ X17 @ X18)
% 0.47/0.65          | ~ (r1_tarski @ X17 @ (k2_xboole_0 @ X18 @ X19))
% 0.47/0.65          | ~ (r1_xboole_0 @ X17 @ X19))),
% 0.47/0.65      inference('cnf', [status(esa)], [t73_xboole_1])).
% 0.47/0.65  thf('54', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.65         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.47/0.65          | ~ (r1_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1))
% 0.47/0.65          | (r1_tarski @ X2 @ X1))),
% 0.47/0.65      inference('sup-', [status(thm)], ['52', '53'])).
% 0.47/0.65  thf('55', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         ((r1_tarski @ X1 @ X0) | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ X0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['51', '54'])).
% 0.47/0.65  thf('56', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.47/0.65      inference('sup-', [status(thm)], ['44', '55'])).
% 0.47/0.65  thf('57', plain,
% 0.47/0.65      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.65         (~ (r1_tarski @ X14 @ X15)
% 0.47/0.65          | ~ (r1_xboole_0 @ X15 @ X16)
% 0.47/0.65          | (r1_xboole_0 @ X14 @ X16))),
% 0.47/0.65      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.47/0.65  thf('58', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.65         ((r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 0.47/0.65          | ~ (r1_xboole_0 @ X0 @ X2))),
% 0.47/0.65      inference('sup-', [status(thm)], ['56', '57'])).
% 0.47/0.65  thf('59', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.65         (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ (k4_xboole_0 @ X1 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['14', '58'])).
% 0.47/0.65  thf('60', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((r1_xboole_0 @ sk_A @ X0)
% 0.47/0.65          | ~ (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C_1) @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['3', '4'])).
% 0.47/0.65  thf('61', plain,
% 0.47/0.65      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))),
% 0.47/0.65      inference('sup-', [status(thm)], ['59', '60'])).
% 0.47/0.65  thf('62', plain,
% 0.47/0.65      (![X4 : $i, X5 : $i]:
% 0.47/0.65         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 0.47/0.65      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.47/0.65  thf('63', plain,
% 0.47/0.65      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A)),
% 0.47/0.65      inference('sup-', [status(thm)], ['61', '62'])).
% 0.47/0.65  thf('64', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (~ (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.47/0.65          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X1))),
% 0.47/0.65      inference('sup-', [status(thm)], ['27', '28'])).
% 0.47/0.65  thf('65', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B)),
% 0.47/0.65      inference('sup-', [status(thm)], ['63', '64'])).
% 0.47/0.65  thf('66', plain,
% 0.47/0.65      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.65         ((r1_tarski @ X11 @ (k2_xboole_0 @ X12 @ X13))
% 0.47/0.65          | ~ (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X13))),
% 0.47/0.65      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.47/0.65  thf('67', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_B))),
% 0.47/0.65      inference('sup-', [status(thm)], ['65', '66'])).
% 0.47/0.65  thf('68', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         ((r1_tarski @ X1 @ X0) | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ X0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['51', '54'])).
% 0.47/0.65  thf('69', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.47/0.65      inference('sup-', [status(thm)], ['67', '68'])).
% 0.47/0.65  thf('70', plain, ($false), inference('demod', [status(thm)], ['11', '69'])).
% 0.47/0.65  
% 0.47/0.65  % SZS output end Refutation
% 0.47/0.65  
% 0.47/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
