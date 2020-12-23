%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vCBIBUXaNO

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:52 EST 2020

% Result     : Theorem 2.87s
% Output     : Refutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 640 expanded)
%              Number of leaves         :   27 ( 209 expanded)
%              Depth                    :   17
%              Number of atoms          :  901 (4770 expanded)
%              Number of equality atoms :   94 ( 490 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t140_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t140_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('1',plain,(
    ! [X45: $i,X47: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X45 ) @ X47 )
      | ~ ( r2_hidden @ X45 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_xboole_0 @ X24 @ X25 )
        = X24 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ( X14 != X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X15: $i] :
      ( r1_tarski @ X15 @ X15 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_xboole_0 @ X24 @ X25 )
        = X24 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('13',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','14'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('17',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','14'])).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('21',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['7','23'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('26',plain,(
    ! [X21: $i] :
      ( ( k2_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X28: $i,X29: $i] :
      ( r1_tarski @ X28 @ ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X14: $i,X16: $i] :
      ( ( X14 = X16 )
      | ~ ( r1_tarski @ X16 @ X14 )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf('33',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','32'])).

thf('34',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('35',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('38',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t99_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) @ ( k4_xboole_0 @ B @ ( k2_xboole_0 @ A @ C ) ) ) ) )).

thf('40',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X32 @ X33 ) @ X34 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X32 @ ( k2_xboole_0 @ X33 @ X34 ) ) @ ( k4_xboole_0 @ X33 @ ( k2_xboole_0 @ X32 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[t99_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('44',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X32 @ X33 ) @ X34 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X32 @ ( k2_xboole_0 @ X33 @ X34 ) ) @ ( k4_xboole_0 @ X33 @ ( k2_xboole_0 @ X32 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[t99_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('50',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('52',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X26 @ X27 ) @ ( k4_xboole_0 @ X26 @ X27 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','57'])).

thf('59',plain,(
    ! [X21: $i] :
      ( ( k2_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','58','59'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('61',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_xboole_0 @ X30 @ X31 )
      = ( k5_xboole_0 @ X30 @ ( k4_xboole_0 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['38','62'])).

thf('64',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','32'])).

thf('65',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('66',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('68',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_xboole_0 @ X30 @ X31 )
      = ( k5_xboole_0 @ X30 @ ( k4_xboole_0 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('70',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('72',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('73',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_xboole_0 @ X20 @ X19 )
        = X19 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('74',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('76',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( sk_B
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','71','76'])).

thf('78',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('79',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('80',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k2_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','32'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('84',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['80','81','82','83'])).

thf('85',plain,
    ( sk_B
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['77','84'])).

thf('86',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['63','85'])).

thf('87',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('89',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
 != sk_B ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('91',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
 != sk_B ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['80','81','82','83'])).

thf('93',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
 != sk_B ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['86','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vCBIBUXaNO
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:31:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.87/3.06  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.87/3.06  % Solved by: fo/fo7.sh
% 2.87/3.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.87/3.06  % done 3999 iterations in 2.614s
% 2.87/3.06  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.87/3.06  % SZS output start Refutation
% 2.87/3.06  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.87/3.06  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.87/3.06  thf(sk_B_type, type, sk_B: $i).
% 2.87/3.06  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.87/3.06  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.87/3.06  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.87/3.06  thf(sk_A_type, type, sk_A: $i).
% 2.87/3.06  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.87/3.06  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.87/3.06  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.87/3.06  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.87/3.06  thf(t140_zfmisc_1, conjecture,
% 2.87/3.06    (![A:$i,B:$i]:
% 2.87/3.06     ( ( r2_hidden @ A @ B ) =>
% 2.87/3.06       ( ( k2_xboole_0 @
% 2.87/3.06           ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 2.87/3.06         ( B ) ) ))).
% 2.87/3.06  thf(zf_stmt_0, negated_conjecture,
% 2.87/3.06    (~( ![A:$i,B:$i]:
% 2.87/3.06        ( ( r2_hidden @ A @ B ) =>
% 2.87/3.06          ( ( k2_xboole_0 @
% 2.87/3.06              ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 2.87/3.06            ( B ) ) ) )),
% 2.87/3.06    inference('cnf.neg', [status(esa)], [t140_zfmisc_1])).
% 2.87/3.06  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 2.87/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.87/3.06  thf(l1_zfmisc_1, axiom,
% 2.87/3.06    (![A:$i,B:$i]:
% 2.87/3.06     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 2.87/3.06  thf('1', plain,
% 2.87/3.06      (![X45 : $i, X47 : $i]:
% 2.87/3.06         ((r1_tarski @ (k1_tarski @ X45) @ X47) | ~ (r2_hidden @ X45 @ X47))),
% 2.87/3.06      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 2.87/3.06  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 2.87/3.06      inference('sup-', [status(thm)], ['0', '1'])).
% 2.87/3.06  thf(t28_xboole_1, axiom,
% 2.87/3.06    (![A:$i,B:$i]:
% 2.87/3.06     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.87/3.06  thf('3', plain,
% 2.87/3.06      (![X24 : $i, X25 : $i]:
% 2.87/3.06         (((k3_xboole_0 @ X24 @ X25) = (X24)) | ~ (r1_tarski @ X24 @ X25))),
% 2.87/3.06      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.87/3.06  thf('4', plain,
% 2.87/3.06      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 2.87/3.06      inference('sup-', [status(thm)], ['2', '3'])).
% 2.87/3.06  thf(t100_xboole_1, axiom,
% 2.87/3.06    (![A:$i,B:$i]:
% 2.87/3.06     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.87/3.06  thf('5', plain,
% 2.87/3.06      (![X17 : $i, X18 : $i]:
% 2.87/3.06         ((k4_xboole_0 @ X17 @ X18)
% 2.87/3.06           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 2.87/3.06      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.87/3.06  thf('6', plain,
% 2.87/3.06      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 2.87/3.06         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 2.87/3.06      inference('sup+', [status(thm)], ['4', '5'])).
% 2.87/3.06  thf(d3_tarski, axiom,
% 2.87/3.06    (![A:$i,B:$i]:
% 2.87/3.06     ( ( r1_tarski @ A @ B ) <=>
% 2.87/3.06       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.87/3.06  thf('7', plain,
% 2.87/3.06      (![X3 : $i, X5 : $i]:
% 2.87/3.06         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 2.87/3.06      inference('cnf', [status(esa)], [d3_tarski])).
% 2.87/3.06  thf(d6_xboole_0, axiom,
% 2.87/3.06    (![A:$i,B:$i]:
% 2.87/3.06     ( ( k5_xboole_0 @ A @ B ) =
% 2.87/3.06       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 2.87/3.06  thf('8', plain,
% 2.87/3.06      (![X12 : $i, X13 : $i]:
% 2.87/3.06         ((k5_xboole_0 @ X12 @ X13)
% 2.87/3.06           = (k2_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ 
% 2.87/3.06              (k4_xboole_0 @ X13 @ X12)))),
% 2.87/3.06      inference('cnf', [status(esa)], [d6_xboole_0])).
% 2.87/3.06  thf(d10_xboole_0, axiom,
% 2.87/3.06    (![A:$i,B:$i]:
% 2.87/3.06     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.87/3.06  thf('9', plain,
% 2.87/3.06      (![X14 : $i, X15 : $i]: ((r1_tarski @ X14 @ X15) | ((X14) != (X15)))),
% 2.87/3.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.87/3.06  thf('10', plain, (![X15 : $i]: (r1_tarski @ X15 @ X15)),
% 2.87/3.06      inference('simplify', [status(thm)], ['9'])).
% 2.87/3.06  thf('11', plain,
% 2.87/3.06      (![X24 : $i, X25 : $i]:
% 2.87/3.06         (((k3_xboole_0 @ X24 @ X25) = (X24)) | ~ (r1_tarski @ X24 @ X25))),
% 2.87/3.06      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.87/3.06  thf('12', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 2.87/3.06      inference('sup-', [status(thm)], ['10', '11'])).
% 2.87/3.06  thf(t22_xboole_1, axiom,
% 2.87/3.06    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 2.87/3.06  thf('13', plain,
% 2.87/3.06      (![X22 : $i, X23 : $i]:
% 2.87/3.06         ((k2_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23)) = (X22))),
% 2.87/3.06      inference('cnf', [status(esa)], [t22_xboole_1])).
% 2.87/3.06  thf('14', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 2.87/3.06      inference('sup+', [status(thm)], ['12', '13'])).
% 2.87/3.06  thf('15', plain,
% 2.87/3.06      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 2.87/3.06      inference('sup+', [status(thm)], ['8', '14'])).
% 2.87/3.06  thf(d5_xboole_0, axiom,
% 2.87/3.06    (![A:$i,B:$i,C:$i]:
% 2.87/3.06     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 2.87/3.06       ( ![D:$i]:
% 2.87/3.06         ( ( r2_hidden @ D @ C ) <=>
% 2.87/3.06           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 2.87/3.06  thf('16', plain,
% 2.87/3.06      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 2.87/3.06         (~ (r2_hidden @ X10 @ X9)
% 2.87/3.06          | (r2_hidden @ X10 @ X7)
% 2.87/3.06          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 2.87/3.06      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.87/3.06  thf('17', plain,
% 2.87/3.06      (![X7 : $i, X8 : $i, X10 : $i]:
% 2.87/3.06         ((r2_hidden @ X10 @ X7)
% 2.87/3.06          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 2.87/3.06      inference('simplify', [status(thm)], ['16'])).
% 2.87/3.06  thf('18', plain,
% 2.87/3.06      (![X0 : $i, X1 : $i]:
% 2.87/3.06         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 2.87/3.06      inference('sup-', [status(thm)], ['15', '17'])).
% 2.87/3.06  thf('19', plain,
% 2.87/3.06      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 2.87/3.06      inference('sup+', [status(thm)], ['8', '14'])).
% 2.87/3.06  thf('20', plain,
% 2.87/3.06      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 2.87/3.06         (~ (r2_hidden @ X10 @ X9)
% 2.87/3.06          | ~ (r2_hidden @ X10 @ X8)
% 2.87/3.06          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 2.87/3.06      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.87/3.06  thf('21', plain,
% 2.87/3.06      (![X7 : $i, X8 : $i, X10 : $i]:
% 2.87/3.06         (~ (r2_hidden @ X10 @ X8)
% 2.87/3.06          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 2.87/3.06      inference('simplify', [status(thm)], ['20'])).
% 2.87/3.06  thf('22', plain,
% 2.87/3.06      (![X0 : $i, X1 : $i]:
% 2.87/3.06         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 2.87/3.06          | ~ (r2_hidden @ X1 @ X0))),
% 2.87/3.06      inference('sup-', [status(thm)], ['19', '21'])).
% 2.87/3.06  thf('23', plain,
% 2.87/3.06      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 2.87/3.06      inference('clc', [status(thm)], ['18', '22'])).
% 2.87/3.06  thf('24', plain,
% 2.87/3.06      (![X0 : $i, X1 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 2.87/3.06      inference('sup-', [status(thm)], ['7', '23'])).
% 2.87/3.06  thf(commutativity_k2_xboole_0, axiom,
% 2.87/3.06    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.87/3.06  thf('25', plain,
% 2.87/3.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.87/3.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.87/3.06  thf(t1_boole, axiom,
% 2.87/3.06    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.87/3.06  thf('26', plain, (![X21 : $i]: ((k2_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 2.87/3.06      inference('cnf', [status(esa)], [t1_boole])).
% 2.87/3.06  thf('27', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.87/3.06      inference('sup+', [status(thm)], ['25', '26'])).
% 2.87/3.06  thf(t7_xboole_1, axiom,
% 2.87/3.06    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.87/3.06  thf('28', plain,
% 2.87/3.06      (![X28 : $i, X29 : $i]: (r1_tarski @ X28 @ (k2_xboole_0 @ X28 @ X29))),
% 2.87/3.06      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.87/3.06  thf('29', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.87/3.06      inference('sup+', [status(thm)], ['27', '28'])).
% 2.87/3.06  thf('30', plain,
% 2.87/3.06      (![X14 : $i, X16 : $i]:
% 2.87/3.06         (((X14) = (X16))
% 2.87/3.06          | ~ (r1_tarski @ X16 @ X14)
% 2.87/3.06          | ~ (r1_tarski @ X14 @ X16))),
% 2.87/3.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.87/3.06  thf('31', plain,
% 2.87/3.06      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 2.87/3.06      inference('sup-', [status(thm)], ['29', '30'])).
% 2.87/3.06  thf('32', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.87/3.06      inference('sup-', [status(thm)], ['24', '31'])).
% 2.87/3.06  thf('33', plain,
% 2.87/3.06      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 2.87/3.06      inference('demod', [status(thm)], ['6', '32'])).
% 2.87/3.06  thf('34', plain,
% 2.87/3.06      (![X12 : $i, X13 : $i]:
% 2.87/3.06         ((k5_xboole_0 @ X12 @ X13)
% 2.87/3.06           = (k2_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ 
% 2.87/3.06              (k4_xboole_0 @ X13 @ X12)))),
% 2.87/3.06      inference('cnf', [status(esa)], [d6_xboole_0])).
% 2.87/3.06  thf('35', plain,
% 2.87/3.06      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 2.87/3.06         = (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 2.87/3.06            k1_xboole_0))),
% 2.87/3.06      inference('sup+', [status(thm)], ['33', '34'])).
% 2.87/3.06  thf('36', plain,
% 2.87/3.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.87/3.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.87/3.06  thf('37', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.87/3.06      inference('sup+', [status(thm)], ['25', '26'])).
% 2.87/3.06  thf('38', plain,
% 2.87/3.06      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 2.87/3.06         = (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 2.87/3.06      inference('demod', [status(thm)], ['35', '36', '37'])).
% 2.87/3.06  thf('39', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 2.87/3.06      inference('sup+', [status(thm)], ['12', '13'])).
% 2.87/3.06  thf(t99_xboole_1, axiom,
% 2.87/3.06    (![A:$i,B:$i,C:$i]:
% 2.87/3.06     ( ( k4_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 2.87/3.06       ( k2_xboole_0 @
% 2.87/3.06         ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) @ 
% 2.87/3.06         ( k4_xboole_0 @ B @ ( k2_xboole_0 @ A @ C ) ) ) ))).
% 2.87/3.06  thf('40', plain,
% 2.87/3.06      (![X32 : $i, X33 : $i, X34 : $i]:
% 2.87/3.06         ((k4_xboole_0 @ (k5_xboole_0 @ X32 @ X33) @ X34)
% 2.87/3.06           = (k2_xboole_0 @ (k4_xboole_0 @ X32 @ (k2_xboole_0 @ X33 @ X34)) @ 
% 2.87/3.06              (k4_xboole_0 @ X33 @ (k2_xboole_0 @ X32 @ X34))))),
% 2.87/3.06      inference('cnf', [status(esa)], [t99_xboole_1])).
% 2.87/3.06  thf('41', plain,
% 2.87/3.06      (![X0 : $i, X1 : $i]:
% 2.87/3.06         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X0)
% 2.87/3.06           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 2.87/3.06              (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 2.87/3.06      inference('sup+', [status(thm)], ['39', '40'])).
% 2.87/3.06  thf('42', plain,
% 2.87/3.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.87/3.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.87/3.06  thf('43', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 2.87/3.06      inference('sup+', [status(thm)], ['12', '13'])).
% 2.87/3.06  thf('44', plain,
% 2.87/3.06      (![X32 : $i, X33 : $i, X34 : $i]:
% 2.87/3.06         ((k4_xboole_0 @ (k5_xboole_0 @ X32 @ X33) @ X34)
% 2.87/3.06           = (k2_xboole_0 @ (k4_xboole_0 @ X32 @ (k2_xboole_0 @ X33 @ X34)) @ 
% 2.87/3.06              (k4_xboole_0 @ X33 @ (k2_xboole_0 @ X32 @ X34))))),
% 2.87/3.06      inference('cnf', [status(esa)], [t99_xboole_1])).
% 2.87/3.06  thf('45', plain,
% 2.87/3.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.87/3.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.87/3.06  thf('46', plain,
% 2.87/3.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.87/3.06         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ X0)) @ 
% 2.87/3.06           (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 2.87/3.06           = (k4_xboole_0 @ (k5_xboole_0 @ X2 @ X1) @ X0))),
% 2.87/3.06      inference('sup+', [status(thm)], ['44', '45'])).
% 2.87/3.06  thf('47', plain,
% 2.87/3.06      (![X0 : $i, X1 : $i]:
% 2.87/3.06         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 2.87/3.06           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0))),
% 2.87/3.06      inference('sup+', [status(thm)], ['43', '46'])).
% 2.87/3.06  thf('48', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.87/3.06      inference('sup-', [status(thm)], ['24', '31'])).
% 2.87/3.06  thf('49', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.87/3.06      inference('sup+', [status(thm)], ['25', '26'])).
% 2.87/3.06  thf('50', plain,
% 2.87/3.06      (![X22 : $i, X23 : $i]:
% 2.87/3.06         ((k2_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23)) = (X22))),
% 2.87/3.06      inference('cnf', [status(esa)], [t22_xboole_1])).
% 2.87/3.06  thf('51', plain,
% 2.87/3.06      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.87/3.06      inference('sup+', [status(thm)], ['49', '50'])).
% 2.87/3.06  thf(t51_xboole_1, axiom,
% 2.87/3.06    (![A:$i,B:$i]:
% 2.87/3.06     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 2.87/3.06       ( A ) ))).
% 2.87/3.06  thf('52', plain,
% 2.87/3.06      (![X26 : $i, X27 : $i]:
% 2.87/3.06         ((k2_xboole_0 @ (k3_xboole_0 @ X26 @ X27) @ (k4_xboole_0 @ X26 @ X27))
% 2.87/3.06           = (X26))),
% 2.87/3.06      inference('cnf', [status(esa)], [t51_xboole_1])).
% 2.87/3.06  thf('53', plain,
% 2.87/3.06      (![X0 : $i]:
% 2.87/3.06         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 2.87/3.06           = (k1_xboole_0))),
% 2.87/3.06      inference('sup+', [status(thm)], ['51', '52'])).
% 2.87/3.06  thf('54', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.87/3.06      inference('sup+', [status(thm)], ['25', '26'])).
% 2.87/3.06  thf('55', plain,
% 2.87/3.06      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.87/3.06      inference('demod', [status(thm)], ['53', '54'])).
% 2.87/3.06  thf('56', plain,
% 2.87/3.06      (![X0 : $i, X1 : $i]:
% 2.87/3.06         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1) = (k1_xboole_0))),
% 2.87/3.06      inference('sup+', [status(thm)], ['48', '55'])).
% 2.87/3.06  thf('57', plain,
% 2.87/3.06      (![X0 : $i, X1 : $i]:
% 2.87/3.06         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 2.87/3.06      inference('demod', [status(thm)], ['47', '56'])).
% 2.87/3.06  thf('58', plain,
% 2.87/3.06      (![X0 : $i, X1 : $i]:
% 2.87/3.06         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 2.87/3.06      inference('sup+', [status(thm)], ['42', '57'])).
% 2.87/3.06  thf('59', plain, (![X21 : $i]: ((k2_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 2.87/3.06      inference('cnf', [status(esa)], [t1_boole])).
% 2.87/3.06  thf('60', plain,
% 2.87/3.06      (![X0 : $i, X1 : $i]:
% 2.87/3.06         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X0)
% 2.87/3.06           = (k4_xboole_0 @ X1 @ X0))),
% 2.87/3.06      inference('demod', [status(thm)], ['41', '58', '59'])).
% 2.87/3.06  thf(t98_xboole_1, axiom,
% 2.87/3.06    (![A:$i,B:$i]:
% 2.87/3.06     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 2.87/3.06  thf('61', plain,
% 2.87/3.06      (![X30 : $i, X31 : $i]:
% 2.87/3.06         ((k2_xboole_0 @ X30 @ X31)
% 2.87/3.06           = (k5_xboole_0 @ X30 @ (k4_xboole_0 @ X31 @ X30)))),
% 2.87/3.06      inference('cnf', [status(esa)], [t98_xboole_1])).
% 2.87/3.06  thf('62', plain,
% 2.87/3.06      (![X0 : $i, X1 : $i]:
% 2.87/3.06         ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 2.87/3.06           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.87/3.06      inference('sup+', [status(thm)], ['60', '61'])).
% 2.87/3.06  thf('63', plain,
% 2.87/3.06      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 2.87/3.06         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 2.87/3.06         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 2.87/3.06            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 2.87/3.06      inference('sup+', [status(thm)], ['38', '62'])).
% 2.87/3.06  thf('64', plain,
% 2.87/3.06      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 2.87/3.06      inference('demod', [status(thm)], ['6', '32'])).
% 2.87/3.06  thf('65', plain,
% 2.87/3.06      (![X12 : $i, X13 : $i]:
% 2.87/3.06         ((k5_xboole_0 @ X12 @ X13)
% 2.87/3.06           = (k2_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ 
% 2.87/3.06              (k4_xboole_0 @ X13 @ X12)))),
% 2.87/3.06      inference('cnf', [status(esa)], [d6_xboole_0])).
% 2.87/3.06  thf('66', plain,
% 2.87/3.06      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 2.87/3.06         = (k2_xboole_0 @ k1_xboole_0 @ 
% 2.87/3.06            (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 2.87/3.06      inference('sup+', [status(thm)], ['64', '65'])).
% 2.87/3.06  thf('67', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.87/3.06      inference('sup+', [status(thm)], ['25', '26'])).
% 2.87/3.06  thf('68', plain,
% 2.87/3.06      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 2.87/3.06         = (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 2.87/3.06      inference('demod', [status(thm)], ['66', '67'])).
% 2.87/3.06  thf('69', plain,
% 2.87/3.06      (![X30 : $i, X31 : $i]:
% 2.87/3.06         ((k2_xboole_0 @ X30 @ X31)
% 2.87/3.06           = (k5_xboole_0 @ X30 @ (k4_xboole_0 @ X31 @ X30)))),
% 2.87/3.06      inference('cnf', [status(esa)], [t98_xboole_1])).
% 2.87/3.06  thf('70', plain,
% 2.87/3.06      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 2.87/3.06         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 2.87/3.06            (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 2.87/3.06      inference('sup+', [status(thm)], ['68', '69'])).
% 2.87/3.06  thf('71', plain,
% 2.87/3.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.87/3.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.87/3.06  thf('72', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 2.87/3.06      inference('sup-', [status(thm)], ['0', '1'])).
% 2.87/3.06  thf(t12_xboole_1, axiom,
% 2.87/3.06    (![A:$i,B:$i]:
% 2.87/3.06     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 2.87/3.06  thf('73', plain,
% 2.87/3.06      (![X19 : $i, X20 : $i]:
% 2.87/3.06         (((k2_xboole_0 @ X20 @ X19) = (X19)) | ~ (r1_tarski @ X20 @ X19))),
% 2.87/3.06      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.87/3.06  thf('74', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))),
% 2.87/3.06      inference('sup-', [status(thm)], ['72', '73'])).
% 2.87/3.06  thf('75', plain,
% 2.87/3.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.87/3.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.87/3.06  thf('76', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 2.87/3.06      inference('demod', [status(thm)], ['74', '75'])).
% 2.87/3.06  thf('77', plain,
% 2.87/3.06      (((sk_B)
% 2.87/3.06         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 2.87/3.06            (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 2.87/3.06      inference('demod', [status(thm)], ['70', '71', '76'])).
% 2.87/3.06  thf('78', plain,
% 2.87/3.06      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 2.87/3.06         = (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 2.87/3.06      inference('demod', [status(thm)], ['66', '67'])).
% 2.87/3.06  thf('79', plain,
% 2.87/3.06      (![X12 : $i, X13 : $i]:
% 2.87/3.06         ((k5_xboole_0 @ X12 @ X13)
% 2.87/3.06           = (k2_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ 
% 2.87/3.06              (k4_xboole_0 @ X13 @ X12)))),
% 2.87/3.06      inference('cnf', [status(esa)], [d6_xboole_0])).
% 2.87/3.06  thf('80', plain,
% 2.87/3.06      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 2.87/3.06         = (k2_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 2.87/3.06            (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 2.87/3.06      inference('sup+', [status(thm)], ['78', '79'])).
% 2.87/3.06  thf('81', plain,
% 2.87/3.06      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 2.87/3.06      inference('demod', [status(thm)], ['6', '32'])).
% 2.87/3.06  thf('82', plain,
% 2.87/3.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.87/3.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.87/3.06  thf('83', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.87/3.06      inference('sup+', [status(thm)], ['25', '26'])).
% 2.87/3.06  thf('84', plain,
% 2.87/3.06      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 2.87/3.06         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 2.87/3.06      inference('demod', [status(thm)], ['80', '81', '82', '83'])).
% 2.87/3.06  thf('85', plain,
% 2.87/3.06      (((sk_B)
% 2.87/3.06         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 2.87/3.06            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 2.87/3.06      inference('demod', [status(thm)], ['77', '84'])).
% 2.87/3.06  thf('86', plain,
% 2.87/3.06      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 2.87/3.06         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) = (sk_B))),
% 2.87/3.06      inference('demod', [status(thm)], ['63', '85'])).
% 2.87/3.06  thf('87', plain,
% 2.87/3.06      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 2.87/3.06         (k1_tarski @ sk_A)) != (sk_B))),
% 2.87/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.87/3.06  thf('88', plain,
% 2.87/3.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.87/3.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.87/3.06  thf('89', plain,
% 2.87/3.06      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 2.87/3.06         (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) != (sk_B))),
% 2.87/3.06      inference('demod', [status(thm)], ['87', '88'])).
% 2.87/3.06  thf('90', plain,
% 2.87/3.06      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 2.87/3.06         = (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 2.87/3.06      inference('demod', [status(thm)], ['66', '67'])).
% 2.87/3.06  thf('91', plain,
% 2.87/3.06      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 2.87/3.06         (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)) != (sk_B))),
% 2.87/3.06      inference('demod', [status(thm)], ['89', '90'])).
% 2.87/3.06  thf('92', plain,
% 2.87/3.06      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 2.87/3.06         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 2.87/3.06      inference('demod', [status(thm)], ['80', '81', '82', '83'])).
% 2.87/3.06  thf('93', plain,
% 2.87/3.06      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 2.87/3.06         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) != (sk_B))),
% 2.87/3.06      inference('demod', [status(thm)], ['91', '92'])).
% 2.87/3.06  thf('94', plain, ($false),
% 2.87/3.06      inference('simplify_reflect-', [status(thm)], ['86', '93'])).
% 2.87/3.06  
% 2.87/3.06  % SZS output end Refutation
% 2.87/3.06  
% 2.87/3.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
