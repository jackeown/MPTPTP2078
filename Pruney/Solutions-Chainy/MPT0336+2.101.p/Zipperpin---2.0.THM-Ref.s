%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W6vWEnsWnY

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:33 EST 2020

% Result     : Theorem 4.39s
% Output     : Refutation 4.39s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 219 expanded)
%              Number of leaves         :   27 (  78 expanded)
%              Depth                    :   21
%              Number of atoms          :  846 (1739 expanded)
%              Number of equality atoms :   35 (  59 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    ! [X37: $i,X38: $i] :
      ( ( ( k4_xboole_0 @ X37 @ ( k1_tarski @ X38 ) )
        = X37 )
      | ( r2_hidden @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ X24 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_xboole_0 @ X17 @ X18 )
      | ( r1_xboole_0 @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_D_1 ) ) @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
      | ( r2_hidden @ sk_D_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_xboole_0 @ X25 @ X26 )
        = X25 )
      | ~ ( r1_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['11','20'])).

thf('22',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('24',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['11','20'])).

thf('26',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('27',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('28',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_D_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('32',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_A )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('33',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) )
      | ~ ( r1_xboole_0 @ X19 @ X20 )
      | ~ ( r1_xboole_0 @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D_1 @ sk_A )
      | ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) )
    | ( r2_hidden @ sk_D_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','34'])).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('37',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_A )
    | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r2_hidden @ sk_D_1 @ sk_A ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D_1 @ X0 )
      | ( r2_hidden @ sk_D_1 @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('43',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('44',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('45',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D_1 @ X0 )
      | ~ ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','46'])).

thf('48',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_D_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['21','47'])).

thf('49',plain,(
    r2_hidden @ sk_D_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k4_xboole_0 @ X37 @ ( k1_tarski @ X38 ) )
        = X37 )
      | ( r2_hidden @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('53',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('54',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X34 @ X35 ) )
      = ( k2_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X19: $i,X20: $i,X22: $i] :
      ( ( r1_xboole_0 @ X19 @ X20 )
      | ~ ( r1_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ ( k3_tarski @ ( k1_tarski @ X0 ) ) )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k3_tarski @ ( k1_tarski @ X0 ) ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) )
      | ~ ( r1_xboole_0 @ X19 @ X20 )
      | ~ ( r1_xboole_0 @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ( r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('65',plain,(
    r1_xboole_0 @ sk_C_1 @ ( k3_tarski @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_xboole_0 @ X25 @ X26 )
        = X25 )
      | ~ ( r1_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('67',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ ( k3_tarski @ ( k1_tarski @ sk_B ) ) )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k3_tarski @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['58','69'])).

thf('71',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['49','70'])).

thf('72',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('73',plain,(
    r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_xboole_0 @ X25 @ X26 )
        = X25 )
      | ~ ( r1_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('75',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_D_1 ) )
    = sk_B ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ X24 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('77',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_xboole_0 @ X25 @ X26 )
        = X25 )
      | ~ ( r1_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X36 @ X37 )
      | ( ( k4_xboole_0 @ X37 @ ( k1_tarski @ X36 ) )
       != X37 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
       != ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ~ ( r2_hidden @ sk_D_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['75','81'])).

thf('83',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['48','82'])).

thf('84',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_xboole_0 @ X25 @ X26 )
        = X25 )
      | ~ ( r1_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('85',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('88',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) )
      | ~ ( r1_xboole_0 @ X19 @ X20 )
      | ~ ( r1_xboole_0 @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X2 )
      | ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_xboole_0 @ X25 @ X26 )
        = X25 )
      | ~ ( r1_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_C_1 ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) )
    = sk_B ),
    inference('sup+',[status(thm)],['85','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('95',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['0','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W6vWEnsWnY
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:34:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 4.39/4.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.39/4.60  % Solved by: fo/fo7.sh
% 4.39/4.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.39/4.60  % done 7339 iterations in 4.136s
% 4.39/4.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.39/4.60  % SZS output start Refutation
% 4.39/4.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.39/4.60  thf(sk_B_type, type, sk_B: $i).
% 4.39/4.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.39/4.60  thf(sk_C_1_type, type, sk_C_1: $i).
% 4.39/4.60  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 4.39/4.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 4.39/4.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.39/4.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 4.39/4.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.39/4.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.39/4.60  thf(sk_A_type, type, sk_A: $i).
% 4.39/4.60  thf(sk_D_1_type, type, sk_D_1: $i).
% 4.39/4.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.39/4.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.39/4.60  thf(t149_zfmisc_1, conjecture,
% 4.39/4.60    (![A:$i,B:$i,C:$i,D:$i]:
% 4.39/4.60     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 4.39/4.60         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 4.39/4.60       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 4.39/4.60  thf(zf_stmt_0, negated_conjecture,
% 4.39/4.60    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 4.39/4.60        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 4.39/4.60            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 4.39/4.60          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 4.39/4.60    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 4.39/4.60  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 4.39/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.60  thf(t65_zfmisc_1, axiom,
% 4.39/4.60    (![A:$i,B:$i]:
% 4.39/4.60     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 4.39/4.60       ( ~( r2_hidden @ B @ A ) ) ))).
% 4.39/4.60  thf('1', plain,
% 4.39/4.60      (![X37 : $i, X38 : $i]:
% 4.39/4.60         (((k4_xboole_0 @ X37 @ (k1_tarski @ X38)) = (X37))
% 4.39/4.60          | (r2_hidden @ X38 @ X37))),
% 4.39/4.60      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 4.39/4.60  thf(t79_xboole_1, axiom,
% 4.39/4.60    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 4.39/4.60  thf('2', plain,
% 4.39/4.60      (![X23 : $i, X24 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ X24)),
% 4.39/4.60      inference('cnf', [status(esa)], [t79_xboole_1])).
% 4.39/4.60  thf(symmetry_r1_xboole_0, axiom,
% 4.39/4.60    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 4.39/4.60  thf('3', plain,
% 4.39/4.60      (![X6 : $i, X7 : $i]:
% 4.39/4.60         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 4.39/4.60      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 4.39/4.60  thf('4', plain,
% 4.39/4.60      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 4.39/4.60      inference('sup-', [status(thm)], ['2', '3'])).
% 4.39/4.60  thf('5', plain,
% 4.39/4.60      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D_1))),
% 4.39/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.60  thf(t63_xboole_1, axiom,
% 4.39/4.60    (![A:$i,B:$i,C:$i]:
% 4.39/4.60     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 4.39/4.60       ( r1_xboole_0 @ A @ C ) ))).
% 4.39/4.60  thf('6', plain,
% 4.39/4.60      (![X16 : $i, X17 : $i, X18 : $i]:
% 4.39/4.60         (~ (r1_tarski @ X16 @ X17)
% 4.39/4.60          | ~ (r1_xboole_0 @ X17 @ X18)
% 4.39/4.60          | (r1_xboole_0 @ X16 @ X18))),
% 4.39/4.60      inference('cnf', [status(esa)], [t63_xboole_1])).
% 4.39/4.60  thf('7', plain,
% 4.39/4.60      (![X0 : $i]:
% 4.39/4.60         ((r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X0)
% 4.39/4.60          | ~ (r1_xboole_0 @ (k1_tarski @ sk_D_1) @ X0))),
% 4.39/4.60      inference('sup-', [status(thm)], ['5', '6'])).
% 4.39/4.60  thf('8', plain,
% 4.39/4.60      (![X0 : $i]:
% 4.39/4.60         (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 4.39/4.60          (k4_xboole_0 @ X0 @ (k1_tarski @ sk_D_1)))),
% 4.39/4.60      inference('sup-', [status(thm)], ['4', '7'])).
% 4.39/4.60  thf('9', plain,
% 4.39/4.60      (![X6 : $i, X7 : $i]:
% 4.39/4.60         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 4.39/4.60      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 4.39/4.60  thf('10', plain,
% 4.39/4.60      (![X0 : $i]:
% 4.39/4.60         (r1_xboole_0 @ (k4_xboole_0 @ X0 @ (k1_tarski @ sk_D_1)) @ 
% 4.39/4.60          (k3_xboole_0 @ sk_A @ sk_B))),
% 4.39/4.60      inference('sup-', [status(thm)], ['8', '9'])).
% 4.39/4.60  thf('11', plain,
% 4.39/4.60      (![X0 : $i]:
% 4.39/4.60         ((r1_xboole_0 @ X0 @ (k3_xboole_0 @ sk_A @ sk_B))
% 4.39/4.60          | (r2_hidden @ sk_D_1 @ X0))),
% 4.39/4.60      inference('sup+', [status(thm)], ['1', '10'])).
% 4.39/4.60  thf(t4_xboole_0, axiom,
% 4.39/4.60    (![A:$i,B:$i]:
% 4.39/4.60     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 4.39/4.60            ( r1_xboole_0 @ A @ B ) ) ) & 
% 4.39/4.60       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 4.39/4.60            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 4.39/4.60  thf('12', plain,
% 4.39/4.60      (![X8 : $i, X9 : $i]:
% 4.39/4.60         ((r1_xboole_0 @ X8 @ X9)
% 4.39/4.60          | (r2_hidden @ (sk_C @ X9 @ X8) @ (k3_xboole_0 @ X8 @ X9)))),
% 4.39/4.60      inference('cnf', [status(esa)], [t4_xboole_0])).
% 4.39/4.60  thf(t48_xboole_1, axiom,
% 4.39/4.60    (![A:$i,B:$i]:
% 4.39/4.60     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.39/4.60  thf('13', plain,
% 4.39/4.60      (![X14 : $i, X15 : $i]:
% 4.39/4.60         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 4.39/4.60           = (k3_xboole_0 @ X14 @ X15))),
% 4.39/4.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.39/4.60  thf('14', plain,
% 4.39/4.60      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 4.39/4.60      inference('sup-', [status(thm)], ['2', '3'])).
% 4.39/4.60  thf(t83_xboole_1, axiom,
% 4.39/4.60    (![A:$i,B:$i]:
% 4.39/4.60     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 4.39/4.60  thf('15', plain,
% 4.39/4.60      (![X25 : $i, X26 : $i]:
% 4.39/4.60         (((k4_xboole_0 @ X25 @ X26) = (X25)) | ~ (r1_xboole_0 @ X25 @ X26))),
% 4.39/4.60      inference('cnf', [status(esa)], [t83_xboole_1])).
% 4.39/4.60  thf('16', plain,
% 4.39/4.60      (![X0 : $i, X1 : $i]:
% 4.39/4.60         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 4.39/4.60      inference('sup-', [status(thm)], ['14', '15'])).
% 4.39/4.60  thf('17', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 4.39/4.60      inference('sup+', [status(thm)], ['13', '16'])).
% 4.39/4.60  thf('18', plain,
% 4.39/4.60      (![X8 : $i, X10 : $i, X11 : $i]:
% 4.39/4.60         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 4.39/4.60          | ~ (r1_xboole_0 @ X8 @ X11))),
% 4.39/4.60      inference('cnf', [status(esa)], [t4_xboole_0])).
% 4.39/4.60  thf('19', plain,
% 4.39/4.60      (![X0 : $i, X1 : $i]:
% 4.39/4.60         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 4.39/4.60      inference('sup-', [status(thm)], ['17', '18'])).
% 4.39/4.60  thf('20', plain,
% 4.39/4.60      (![X0 : $i, X1 : $i]:
% 4.39/4.60         ((r1_xboole_0 @ X1 @ X0)
% 4.39/4.60          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 4.39/4.60      inference('sup-', [status(thm)], ['12', '19'])).
% 4.39/4.60  thf('21', plain,
% 4.39/4.60      (((r2_hidden @ sk_D_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 4.39/4.60        | (r1_xboole_0 @ sk_A @ sk_B))),
% 4.39/4.60      inference('sup-', [status(thm)], ['11', '20'])).
% 4.39/4.60  thf('22', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 4.39/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.60  thf('23', plain,
% 4.39/4.60      (![X6 : $i, X7 : $i]:
% 4.39/4.60         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 4.39/4.60      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 4.39/4.60  thf('24', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 4.39/4.60      inference('sup-', [status(thm)], ['22', '23'])).
% 4.39/4.60  thf('25', plain,
% 4.39/4.60      (((r2_hidden @ sk_D_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 4.39/4.60        | (r1_xboole_0 @ sk_A @ sk_B))),
% 4.39/4.60      inference('sup-', [status(thm)], ['11', '20'])).
% 4.39/4.60  thf('26', plain,
% 4.39/4.60      (![X14 : $i, X15 : $i]:
% 4.39/4.60         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 4.39/4.60           = (k3_xboole_0 @ X14 @ X15))),
% 4.39/4.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.39/4.60  thf(d5_xboole_0, axiom,
% 4.39/4.60    (![A:$i,B:$i,C:$i]:
% 4.39/4.60     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 4.39/4.60       ( ![D:$i]:
% 4.39/4.60         ( ( r2_hidden @ D @ C ) <=>
% 4.39/4.60           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 4.39/4.60  thf('27', plain,
% 4.39/4.60      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.39/4.60         (~ (r2_hidden @ X4 @ X3)
% 4.39/4.60          | (r2_hidden @ X4 @ X1)
% 4.39/4.60          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 4.39/4.60      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.39/4.60  thf('28', plain,
% 4.39/4.60      (![X1 : $i, X2 : $i, X4 : $i]:
% 4.39/4.60         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 4.39/4.60      inference('simplify', [status(thm)], ['27'])).
% 4.39/4.60  thf('29', plain,
% 4.39/4.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.39/4.60         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 4.39/4.60      inference('sup-', [status(thm)], ['26', '28'])).
% 4.39/4.60  thf('30', plain,
% 4.39/4.60      (((r1_xboole_0 @ sk_A @ sk_B) | (r2_hidden @ sk_D_1 @ sk_A))),
% 4.39/4.60      inference('sup-', [status(thm)], ['25', '29'])).
% 4.39/4.60  thf('31', plain,
% 4.39/4.60      (![X6 : $i, X7 : $i]:
% 4.39/4.60         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 4.39/4.60      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 4.39/4.60  thf('32', plain,
% 4.39/4.60      (((r2_hidden @ sk_D_1 @ sk_A) | (r1_xboole_0 @ sk_B @ sk_A))),
% 4.39/4.60      inference('sup-', [status(thm)], ['30', '31'])).
% 4.39/4.60  thf(t70_xboole_1, axiom,
% 4.39/4.60    (![A:$i,B:$i,C:$i]:
% 4.39/4.60     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 4.39/4.60            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 4.39/4.60       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 4.39/4.60            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 4.39/4.60  thf('33', plain,
% 4.39/4.60      (![X19 : $i, X20 : $i, X21 : $i]:
% 4.39/4.60         ((r1_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21))
% 4.39/4.60          | ~ (r1_xboole_0 @ X19 @ X20)
% 4.39/4.60          | ~ (r1_xboole_0 @ X19 @ X21))),
% 4.39/4.60      inference('cnf', [status(esa)], [t70_xboole_1])).
% 4.39/4.60  thf('34', plain,
% 4.39/4.60      (![X0 : $i]:
% 4.39/4.60         ((r2_hidden @ sk_D_1 @ sk_A)
% 4.39/4.60          | ~ (r1_xboole_0 @ sk_B @ X0)
% 4.39/4.60          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 4.39/4.60      inference('sup-', [status(thm)], ['32', '33'])).
% 4.39/4.60  thf('35', plain,
% 4.39/4.60      (((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1))
% 4.39/4.60        | (r2_hidden @ sk_D_1 @ sk_A))),
% 4.39/4.60      inference('sup-', [status(thm)], ['24', '34'])).
% 4.39/4.60  thf('36', plain,
% 4.39/4.60      (![X6 : $i, X7 : $i]:
% 4.39/4.60         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 4.39/4.60      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 4.39/4.60  thf('37', plain,
% 4.39/4.60      (((r2_hidden @ sk_D_1 @ sk_A)
% 4.39/4.60        | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B))),
% 4.39/4.60      inference('sup-', [status(thm)], ['35', '36'])).
% 4.39/4.60  thf('38', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 4.39/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.60  thf('39', plain, ((r2_hidden @ sk_D_1 @ sk_A)),
% 4.39/4.60      inference('clc', [status(thm)], ['37', '38'])).
% 4.39/4.60  thf('40', plain,
% 4.39/4.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.39/4.60         (~ (r2_hidden @ X0 @ X1)
% 4.39/4.60          | (r2_hidden @ X0 @ X2)
% 4.39/4.60          | (r2_hidden @ X0 @ X3)
% 4.39/4.60          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 4.39/4.60      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.39/4.60  thf('41', plain,
% 4.39/4.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.39/4.60         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 4.39/4.60          | (r2_hidden @ X0 @ X2)
% 4.39/4.60          | ~ (r2_hidden @ X0 @ X1))),
% 4.39/4.60      inference('simplify', [status(thm)], ['40'])).
% 4.39/4.60  thf('42', plain,
% 4.39/4.60      (![X0 : $i]:
% 4.39/4.60         ((r2_hidden @ sk_D_1 @ X0)
% 4.39/4.60          | (r2_hidden @ sk_D_1 @ (k4_xboole_0 @ sk_A @ X0)))),
% 4.39/4.60      inference('sup-', [status(thm)], ['39', '41'])).
% 4.39/4.60  thf(t47_xboole_1, axiom,
% 4.39/4.60    (![A:$i,B:$i]:
% 4.39/4.60     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 4.39/4.60  thf('43', plain,
% 4.39/4.60      (![X12 : $i, X13 : $i]:
% 4.39/4.60         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 4.39/4.60           = (k4_xboole_0 @ X12 @ X13))),
% 4.39/4.60      inference('cnf', [status(esa)], [t47_xboole_1])).
% 4.39/4.60  thf('44', plain,
% 4.39/4.60      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.39/4.60         (~ (r2_hidden @ X4 @ X3)
% 4.39/4.60          | ~ (r2_hidden @ X4 @ X2)
% 4.39/4.60          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 4.39/4.60      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.39/4.60  thf('45', plain,
% 4.39/4.60      (![X1 : $i, X2 : $i, X4 : $i]:
% 4.39/4.60         (~ (r2_hidden @ X4 @ X2)
% 4.39/4.60          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 4.39/4.60      inference('simplify', [status(thm)], ['44'])).
% 4.39/4.60  thf('46', plain,
% 4.39/4.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.39/4.60         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 4.39/4.60          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 4.39/4.60      inference('sup-', [status(thm)], ['43', '45'])).
% 4.39/4.60  thf('47', plain,
% 4.39/4.60      (![X0 : $i]:
% 4.39/4.60         ((r2_hidden @ sk_D_1 @ X0)
% 4.39/4.60          | ~ (r2_hidden @ sk_D_1 @ (k3_xboole_0 @ sk_A @ X0)))),
% 4.39/4.60      inference('sup-', [status(thm)], ['42', '46'])).
% 4.39/4.60  thf('48', plain,
% 4.39/4.60      (((r1_xboole_0 @ sk_A @ sk_B) | (r2_hidden @ sk_D_1 @ sk_B))),
% 4.39/4.60      inference('sup-', [status(thm)], ['21', '47'])).
% 4.39/4.60  thf('49', plain, ((r2_hidden @ sk_D_1 @ sk_C_1)),
% 4.39/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.60  thf('50', plain,
% 4.39/4.60      (![X37 : $i, X38 : $i]:
% 4.39/4.60         (((k4_xboole_0 @ X37 @ (k1_tarski @ X38)) = (X37))
% 4.39/4.60          | (r2_hidden @ X38 @ X37))),
% 4.39/4.60      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 4.39/4.60  thf('51', plain,
% 4.39/4.60      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 4.39/4.60      inference('sup-', [status(thm)], ['2', '3'])).
% 4.39/4.60  thf('52', plain,
% 4.39/4.60      (![X0 : $i, X1 : $i]:
% 4.39/4.60         ((r1_xboole_0 @ (k1_tarski @ X1) @ X0) | (r2_hidden @ X1 @ X0))),
% 4.39/4.60      inference('sup+', [status(thm)], ['50', '51'])).
% 4.39/4.60  thf(t69_enumset1, axiom,
% 4.39/4.60    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 4.39/4.60  thf('53', plain,
% 4.39/4.60      (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 4.39/4.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.39/4.60  thf(l51_zfmisc_1, axiom,
% 4.39/4.60    (![A:$i,B:$i]:
% 4.39/4.60     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 4.39/4.60  thf('54', plain,
% 4.39/4.60      (![X34 : $i, X35 : $i]:
% 4.39/4.60         ((k3_tarski @ (k2_tarski @ X34 @ X35)) = (k2_xboole_0 @ X34 @ X35))),
% 4.39/4.60      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.39/4.60  thf('55', plain,
% 4.39/4.60      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 4.39/4.60      inference('sup+', [status(thm)], ['53', '54'])).
% 4.39/4.60  thf('56', plain,
% 4.39/4.60      (![X19 : $i, X20 : $i, X22 : $i]:
% 4.39/4.60         ((r1_xboole_0 @ X19 @ X20)
% 4.39/4.60          | ~ (r1_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X22)))),
% 4.39/4.60      inference('cnf', [status(esa)], [t70_xboole_1])).
% 4.39/4.60  thf('57', plain,
% 4.39/4.60      (![X0 : $i, X1 : $i]:
% 4.39/4.60         (~ (r1_xboole_0 @ X1 @ (k3_tarski @ (k1_tarski @ X0)))
% 4.39/4.60          | (r1_xboole_0 @ X1 @ X0))),
% 4.39/4.60      inference('sup-', [status(thm)], ['55', '56'])).
% 4.39/4.60  thf('58', plain,
% 4.39/4.60      (![X0 : $i, X1 : $i]:
% 4.39/4.60         ((r2_hidden @ X1 @ (k3_tarski @ (k1_tarski @ X0)))
% 4.39/4.60          | (r1_xboole_0 @ (k1_tarski @ X1) @ X0))),
% 4.39/4.60      inference('sup-', [status(thm)], ['52', '57'])).
% 4.39/4.60  thf('59', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 4.39/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.60  thf('60', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 4.39/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.60  thf('61', plain,
% 4.39/4.60      (![X19 : $i, X20 : $i, X21 : $i]:
% 4.39/4.60         ((r1_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21))
% 4.39/4.60          | ~ (r1_xboole_0 @ X19 @ X20)
% 4.39/4.60          | ~ (r1_xboole_0 @ X19 @ X21))),
% 4.39/4.60      inference('cnf', [status(esa)], [t70_xboole_1])).
% 4.39/4.60  thf('62', plain,
% 4.39/4.60      (![X0 : $i]:
% 4.39/4.60         (~ (r1_xboole_0 @ sk_C_1 @ X0)
% 4.39/4.60          | (r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ X0)))),
% 4.39/4.60      inference('sup-', [status(thm)], ['60', '61'])).
% 4.39/4.60  thf('63', plain, ((r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_B))),
% 4.39/4.60      inference('sup-', [status(thm)], ['59', '62'])).
% 4.39/4.60  thf('64', plain,
% 4.39/4.60      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 4.39/4.60      inference('sup+', [status(thm)], ['53', '54'])).
% 4.39/4.60  thf('65', plain, ((r1_xboole_0 @ sk_C_1 @ (k3_tarski @ (k1_tarski @ sk_B)))),
% 4.39/4.60      inference('demod', [status(thm)], ['63', '64'])).
% 4.39/4.60  thf('66', plain,
% 4.39/4.60      (![X25 : $i, X26 : $i]:
% 4.39/4.60         (((k4_xboole_0 @ X25 @ X26) = (X25)) | ~ (r1_xboole_0 @ X25 @ X26))),
% 4.39/4.60      inference('cnf', [status(esa)], [t83_xboole_1])).
% 4.39/4.60  thf('67', plain,
% 4.39/4.60      (((k4_xboole_0 @ sk_C_1 @ (k3_tarski @ (k1_tarski @ sk_B))) = (sk_C_1))),
% 4.39/4.60      inference('sup-', [status(thm)], ['65', '66'])).
% 4.39/4.60  thf('68', plain,
% 4.39/4.60      (![X1 : $i, X2 : $i, X4 : $i]:
% 4.39/4.60         (~ (r2_hidden @ X4 @ X2)
% 4.39/4.60          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 4.39/4.60      inference('simplify', [status(thm)], ['44'])).
% 4.39/4.60  thf('69', plain,
% 4.39/4.60      (![X0 : $i]:
% 4.39/4.60         (~ (r2_hidden @ X0 @ sk_C_1)
% 4.39/4.60          | ~ (r2_hidden @ X0 @ (k3_tarski @ (k1_tarski @ sk_B))))),
% 4.39/4.60      inference('sup-', [status(thm)], ['67', '68'])).
% 4.39/4.60  thf('70', plain,
% 4.39/4.60      (![X0 : $i]:
% 4.39/4.60         ((r1_xboole_0 @ (k1_tarski @ X0) @ sk_B) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 4.39/4.60      inference('sup-', [status(thm)], ['58', '69'])).
% 4.39/4.60  thf('71', plain, ((r1_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_B)),
% 4.39/4.60      inference('sup-', [status(thm)], ['49', '70'])).
% 4.39/4.60  thf('72', plain,
% 4.39/4.60      (![X6 : $i, X7 : $i]:
% 4.39/4.60         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 4.39/4.60      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 4.39/4.60  thf('73', plain, ((r1_xboole_0 @ sk_B @ (k1_tarski @ sk_D_1))),
% 4.39/4.60      inference('sup-', [status(thm)], ['71', '72'])).
% 4.39/4.60  thf('74', plain,
% 4.39/4.60      (![X25 : $i, X26 : $i]:
% 4.39/4.60         (((k4_xboole_0 @ X25 @ X26) = (X25)) | ~ (r1_xboole_0 @ X25 @ X26))),
% 4.39/4.60      inference('cnf', [status(esa)], [t83_xboole_1])).
% 4.39/4.60  thf('75', plain, (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_D_1)) = (sk_B))),
% 4.39/4.60      inference('sup-', [status(thm)], ['73', '74'])).
% 4.39/4.60  thf('76', plain,
% 4.39/4.60      (![X23 : $i, X24 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ X24)),
% 4.39/4.60      inference('cnf', [status(esa)], [t79_xboole_1])).
% 4.39/4.60  thf('77', plain,
% 4.39/4.60      (![X25 : $i, X26 : $i]:
% 4.39/4.60         (((k4_xboole_0 @ X25 @ X26) = (X25)) | ~ (r1_xboole_0 @ X25 @ X26))),
% 4.39/4.60      inference('cnf', [status(esa)], [t83_xboole_1])).
% 4.39/4.60  thf('78', plain,
% 4.39/4.60      (![X0 : $i, X1 : $i]:
% 4.39/4.60         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 4.39/4.60           = (k4_xboole_0 @ X1 @ X0))),
% 4.39/4.60      inference('sup-', [status(thm)], ['76', '77'])).
% 4.39/4.60  thf('79', plain,
% 4.39/4.60      (![X36 : $i, X37 : $i]:
% 4.39/4.60         (~ (r2_hidden @ X36 @ X37)
% 4.39/4.60          | ((k4_xboole_0 @ X37 @ (k1_tarski @ X36)) != (X37)))),
% 4.39/4.60      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 4.39/4.60  thf('80', plain,
% 4.39/4.60      (![X0 : $i, X1 : $i]:
% 4.39/4.60         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0))
% 4.39/4.60            != (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 4.39/4.60          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 4.39/4.60      inference('sup-', [status(thm)], ['78', '79'])).
% 4.39/4.60  thf('81', plain,
% 4.39/4.60      (![X0 : $i, X1 : $i]:
% 4.39/4.60         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 4.39/4.60      inference('simplify', [status(thm)], ['80'])).
% 4.39/4.60  thf('82', plain, (~ (r2_hidden @ sk_D_1 @ sk_B)),
% 4.39/4.60      inference('sup-', [status(thm)], ['75', '81'])).
% 4.39/4.60  thf('83', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 4.39/4.60      inference('clc', [status(thm)], ['48', '82'])).
% 4.39/4.60  thf('84', plain,
% 4.39/4.60      (![X25 : $i, X26 : $i]:
% 4.39/4.60         (((k4_xboole_0 @ X25 @ X26) = (X25)) | ~ (r1_xboole_0 @ X25 @ X26))),
% 4.39/4.60      inference('cnf', [status(esa)], [t83_xboole_1])).
% 4.39/4.60  thf('85', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 4.39/4.60      inference('sup-', [status(thm)], ['83', '84'])).
% 4.39/4.60  thf('86', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 4.39/4.60      inference('sup-', [status(thm)], ['22', '23'])).
% 4.39/4.60  thf('87', plain,
% 4.39/4.60      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 4.39/4.60      inference('sup-', [status(thm)], ['2', '3'])).
% 4.39/4.60  thf('88', plain,
% 4.39/4.60      (![X19 : $i, X20 : $i, X21 : $i]:
% 4.39/4.60         ((r1_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21))
% 4.39/4.60          | ~ (r1_xboole_0 @ X19 @ X20)
% 4.39/4.60          | ~ (r1_xboole_0 @ X19 @ X21))),
% 4.39/4.60      inference('cnf', [status(esa)], [t70_xboole_1])).
% 4.39/4.60  thf('89', plain,
% 4.39/4.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.39/4.60         (~ (r1_xboole_0 @ X0 @ X2)
% 4.39/4.60          | (r1_xboole_0 @ X0 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 4.39/4.60      inference('sup-', [status(thm)], ['87', '88'])).
% 4.39/4.60  thf('90', plain,
% 4.39/4.60      (![X0 : $i]:
% 4.39/4.60         (r1_xboole_0 @ sk_B @ 
% 4.39/4.60          (k2_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_C_1))),
% 4.39/4.60      inference('sup-', [status(thm)], ['86', '89'])).
% 4.39/4.60  thf('91', plain,
% 4.39/4.60      (![X25 : $i, X26 : $i]:
% 4.39/4.60         (((k4_xboole_0 @ X25 @ X26) = (X25)) | ~ (r1_xboole_0 @ X25 @ X26))),
% 4.39/4.60      inference('cnf', [status(esa)], [t83_xboole_1])).
% 4.39/4.60  thf('92', plain,
% 4.39/4.60      (![X0 : $i]:
% 4.39/4.60         ((k4_xboole_0 @ sk_B @ 
% 4.39/4.60           (k2_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_C_1)) = (sk_B))),
% 4.39/4.60      inference('sup-', [status(thm)], ['90', '91'])).
% 4.39/4.60  thf('93', plain,
% 4.39/4.60      (((k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1)) = (sk_B))),
% 4.39/4.60      inference('sup+', [status(thm)], ['85', '92'])).
% 4.39/4.60  thf('94', plain,
% 4.39/4.60      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 4.39/4.60      inference('sup-', [status(thm)], ['2', '3'])).
% 4.39/4.60  thf('95', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 4.39/4.60      inference('sup+', [status(thm)], ['93', '94'])).
% 4.39/4.60  thf('96', plain, ($false), inference('demod', [status(thm)], ['0', '95'])).
% 4.39/4.60  
% 4.39/4.60  % SZS output end Refutation
% 4.39/4.60  
% 4.39/4.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
