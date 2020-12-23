%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7qfqf7W8Ba

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:22 EST 2020

% Result     : Theorem 7.52s
% Output     : Refutation 7.52s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 133 expanded)
%              Number of leaves         :   17 (  45 expanded)
%              Depth                    :   14
%              Number of atoms          :  802 (1322 expanded)
%              Number of equality atoms :   38 (  67 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('0',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

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

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('4',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('10',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k3_xboole_0 @ X12 @ X15 ) )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t52_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
          = ( k1_tarski @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_zfmisc_1])).

thf('15',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('17',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','27'])).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('30',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('32',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('36',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('41',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C_1 @ X13 @ X12 ) @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('44',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( X21 = X18 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('45',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C_1 @ X13 @ X12 ) @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('48',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ X2 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X2 ) @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','53'])).

thf('55',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['55'])).

thf('57',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['55'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['55'])).

thf('63',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ sk_A )
      = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['54','66'])).

thf('68',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['0','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('70',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['70','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7qfqf7W8Ba
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:54:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 7.52/7.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 7.52/7.74  % Solved by: fo/fo7.sh
% 7.52/7.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.52/7.74  % done 9964 iterations in 7.277s
% 7.52/7.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 7.52/7.74  % SZS output start Refutation
% 7.52/7.74  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 7.52/7.74  thf(sk_B_type, type, sk_B: $i).
% 7.52/7.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 7.52/7.74  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 7.52/7.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.52/7.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 7.52/7.74  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 7.52/7.74  thf(sk_A_type, type, sk_A: $i).
% 7.52/7.74  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 7.52/7.74  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 7.52/7.74  thf(t48_xboole_1, axiom,
% 7.52/7.74    (![A:$i,B:$i]:
% 7.52/7.74     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 7.52/7.74  thf('0', plain,
% 7.52/7.74      (![X16 : $i, X17 : $i]:
% 7.52/7.74         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 7.52/7.74           = (k3_xboole_0 @ X16 @ X17))),
% 7.52/7.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 7.52/7.74  thf(t3_xboole_0, axiom,
% 7.52/7.74    (![A:$i,B:$i]:
% 7.52/7.74     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 7.52/7.74            ( r1_xboole_0 @ A @ B ) ) ) & 
% 7.52/7.74       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 7.52/7.74            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 7.52/7.74  thf('1', plain,
% 7.52/7.74      (![X8 : $i, X9 : $i]:
% 7.52/7.74         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X9))),
% 7.52/7.74      inference('cnf', [status(esa)], [t3_xboole_0])).
% 7.52/7.74  thf('2', plain,
% 7.52/7.74      (![X8 : $i, X9 : $i]:
% 7.52/7.74         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 7.52/7.74      inference('cnf', [status(esa)], [t3_xboole_0])).
% 7.52/7.74  thf(d5_xboole_0, axiom,
% 7.52/7.74    (![A:$i,B:$i,C:$i]:
% 7.52/7.74     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 7.52/7.74       ( ![D:$i]:
% 7.52/7.74         ( ( r2_hidden @ D @ C ) <=>
% 7.52/7.74           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 7.52/7.74  thf('3', plain,
% 7.52/7.74      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 7.52/7.74         (~ (r2_hidden @ X6 @ X5)
% 7.52/7.74          | ~ (r2_hidden @ X6 @ X4)
% 7.52/7.74          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 7.52/7.74      inference('cnf', [status(esa)], [d5_xboole_0])).
% 7.52/7.74  thf('4', plain,
% 7.52/7.74      (![X3 : $i, X4 : $i, X6 : $i]:
% 7.52/7.74         (~ (r2_hidden @ X6 @ X4)
% 7.52/7.74          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 7.52/7.74      inference('simplify', [status(thm)], ['3'])).
% 7.52/7.74  thf('5', plain,
% 7.52/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.52/7.74         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 7.52/7.74          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 7.52/7.74      inference('sup-', [status(thm)], ['2', '4'])).
% 7.52/7.74  thf('6', plain,
% 7.52/7.74      (![X0 : $i, X1 : $i]:
% 7.52/7.74         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 7.52/7.74          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 7.52/7.74      inference('sup-', [status(thm)], ['1', '5'])).
% 7.52/7.74  thf('7', plain,
% 7.52/7.74      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 7.52/7.74      inference('simplify', [status(thm)], ['6'])).
% 7.52/7.74  thf('8', plain,
% 7.52/7.74      (![X8 : $i, X9 : $i]:
% 7.52/7.74         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 7.52/7.74      inference('cnf', [status(esa)], [t3_xboole_0])).
% 7.52/7.74  thf(commutativity_k3_xboole_0, axiom,
% 7.52/7.74    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 7.52/7.74  thf('9', plain,
% 7.52/7.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 7.52/7.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.52/7.74  thf(t4_xboole_0, axiom,
% 7.52/7.74    (![A:$i,B:$i]:
% 7.52/7.74     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 7.52/7.74            ( r1_xboole_0 @ A @ B ) ) ) & 
% 7.52/7.74       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 7.52/7.74            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 7.52/7.74  thf('10', plain,
% 7.52/7.74      (![X12 : $i, X14 : $i, X15 : $i]:
% 7.52/7.74         (~ (r2_hidden @ X14 @ (k3_xboole_0 @ X12 @ X15))
% 7.52/7.74          | ~ (r1_xboole_0 @ X12 @ X15))),
% 7.52/7.74      inference('cnf', [status(esa)], [t4_xboole_0])).
% 7.52/7.74  thf('11', plain,
% 7.52/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.52/7.74         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 7.52/7.74          | ~ (r1_xboole_0 @ X0 @ X1))),
% 7.52/7.74      inference('sup-', [status(thm)], ['9', '10'])).
% 7.52/7.74  thf('12', plain,
% 7.52/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.52/7.74         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 7.52/7.74          | ~ (r1_xboole_0 @ X0 @ X1))),
% 7.52/7.74      inference('sup-', [status(thm)], ['8', '11'])).
% 7.52/7.74  thf('13', plain,
% 7.52/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.52/7.74         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X2)),
% 7.52/7.74      inference('sup-', [status(thm)], ['7', '12'])).
% 7.52/7.74  thf('14', plain,
% 7.52/7.74      (![X16 : $i, X17 : $i]:
% 7.52/7.74         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 7.52/7.74           = (k3_xboole_0 @ X16 @ X17))),
% 7.52/7.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 7.52/7.74  thf(t52_zfmisc_1, conjecture,
% 7.52/7.74    (![A:$i,B:$i]:
% 7.52/7.74     ( ( r2_hidden @ A @ B ) =>
% 7.52/7.74       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 7.52/7.74  thf(zf_stmt_0, negated_conjecture,
% 7.52/7.74    (~( ![A:$i,B:$i]:
% 7.52/7.74        ( ( r2_hidden @ A @ B ) =>
% 7.52/7.74          ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ) )),
% 7.52/7.74    inference('cnf.neg', [status(esa)], [t52_zfmisc_1])).
% 7.52/7.74  thf('15', plain, ((r2_hidden @ sk_A @ sk_B)),
% 7.52/7.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.52/7.74  thf('16', plain,
% 7.52/7.74      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 7.52/7.74         (~ (r2_hidden @ X2 @ X3)
% 7.52/7.74          | (r2_hidden @ X2 @ X4)
% 7.52/7.74          | (r2_hidden @ X2 @ X5)
% 7.52/7.74          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 7.52/7.74      inference('cnf', [status(esa)], [d5_xboole_0])).
% 7.52/7.74  thf('17', plain,
% 7.52/7.74      (![X2 : $i, X3 : $i, X4 : $i]:
% 7.52/7.74         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 7.52/7.74          | (r2_hidden @ X2 @ X4)
% 7.52/7.74          | ~ (r2_hidden @ X2 @ X3))),
% 7.52/7.74      inference('simplify', [status(thm)], ['16'])).
% 7.52/7.74  thf('18', plain,
% 7.52/7.74      (![X0 : $i]:
% 7.52/7.74         ((r2_hidden @ sk_A @ X0)
% 7.52/7.74          | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 7.52/7.74      inference('sup-', [status(thm)], ['15', '17'])).
% 7.52/7.74  thf('19', plain,
% 7.52/7.74      (![X16 : $i, X17 : $i]:
% 7.52/7.74         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 7.52/7.74           = (k3_xboole_0 @ X16 @ X17))),
% 7.52/7.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 7.52/7.74  thf('20', plain,
% 7.52/7.74      (![X0 : $i]:
% 7.52/7.74         ((r2_hidden @ sk_A @ X0)
% 7.52/7.74          | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 7.52/7.74      inference('sup-', [status(thm)], ['15', '17'])).
% 7.52/7.74  thf('21', plain,
% 7.52/7.74      (![X0 : $i]:
% 7.52/7.74         ((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 7.52/7.74          | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 7.52/7.74      inference('sup+', [status(thm)], ['19', '20'])).
% 7.52/7.74  thf('22', plain,
% 7.52/7.74      (![X3 : $i, X4 : $i, X6 : $i]:
% 7.52/7.74         (~ (r2_hidden @ X6 @ X4)
% 7.52/7.74          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 7.52/7.74      inference('simplify', [status(thm)], ['3'])).
% 7.52/7.74  thf('23', plain,
% 7.52/7.74      (![X0 : $i]:
% 7.52/7.74         ((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 7.52/7.74          | ~ (r2_hidden @ sk_A @ X0))),
% 7.52/7.74      inference('sup-', [status(thm)], ['21', '22'])).
% 7.52/7.74  thf('24', plain,
% 7.52/7.74      (![X0 : $i]:
% 7.52/7.74         ((r2_hidden @ sk_A @ X0)
% 7.52/7.74          | (r2_hidden @ sk_A @ 
% 7.52/7.74             (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ X0))))),
% 7.52/7.74      inference('sup-', [status(thm)], ['18', '23'])).
% 7.52/7.74  thf('25', plain,
% 7.52/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.52/7.74         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 7.52/7.74          | ~ (r1_xboole_0 @ X0 @ X1))),
% 7.52/7.74      inference('sup-', [status(thm)], ['9', '10'])).
% 7.52/7.74  thf('26', plain,
% 7.52/7.74      (![X0 : $i]:
% 7.52/7.74         ((r2_hidden @ sk_A @ X0)
% 7.52/7.74          | ~ (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ sk_B))),
% 7.52/7.74      inference('sup-', [status(thm)], ['24', '25'])).
% 7.52/7.74  thf('27', plain,
% 7.52/7.74      (![X0 : $i]:
% 7.52/7.74         (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ sk_B)
% 7.52/7.74          | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 7.52/7.74      inference('sup-', [status(thm)], ['14', '26'])).
% 7.52/7.74  thf('28', plain,
% 7.52/7.74      (![X0 : $i]:
% 7.52/7.74         (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_B)))),
% 7.52/7.74      inference('sup-', [status(thm)], ['13', '27'])).
% 7.52/7.74  thf('29', plain,
% 7.52/7.74      (![X8 : $i, X9 : $i]:
% 7.52/7.74         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 7.52/7.74      inference('cnf', [status(esa)], [t3_xboole_0])).
% 7.52/7.74  thf('30', plain,
% 7.52/7.74      (![X16 : $i, X17 : $i]:
% 7.52/7.74         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 7.52/7.74           = (k3_xboole_0 @ X16 @ X17))),
% 7.52/7.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 7.52/7.74  thf('31', plain,
% 7.52/7.74      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 7.52/7.74         (~ (r2_hidden @ X6 @ X5)
% 7.52/7.74          | (r2_hidden @ X6 @ X3)
% 7.52/7.74          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 7.52/7.74      inference('cnf', [status(esa)], [d5_xboole_0])).
% 7.52/7.74  thf('32', plain,
% 7.52/7.74      (![X3 : $i, X4 : $i, X6 : $i]:
% 7.52/7.74         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 7.52/7.74      inference('simplify', [status(thm)], ['31'])).
% 7.52/7.74  thf('33', plain,
% 7.52/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.52/7.74         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 7.52/7.74      inference('sup-', [status(thm)], ['30', '32'])).
% 7.52/7.74  thf('34', plain,
% 7.52/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.52/7.74         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 7.52/7.74          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 7.52/7.74      inference('sup-', [status(thm)], ['29', '33'])).
% 7.52/7.74  thf('35', plain,
% 7.52/7.74      (![X8 : $i, X9 : $i]:
% 7.52/7.74         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X9))),
% 7.52/7.74      inference('cnf', [status(esa)], [t3_xboole_0])).
% 7.52/7.74  thf('36', plain,
% 7.52/7.74      (![X3 : $i, X4 : $i, X6 : $i]:
% 7.52/7.74         (~ (r2_hidden @ X6 @ X4)
% 7.52/7.74          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 7.52/7.74      inference('simplify', [status(thm)], ['3'])).
% 7.52/7.74  thf('37', plain,
% 7.52/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.52/7.74         ((r1_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 7.52/7.74          | ~ (r2_hidden @ (sk_C @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 7.52/7.74      inference('sup-', [status(thm)], ['35', '36'])).
% 7.52/7.74  thf('38', plain,
% 7.52/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.52/7.74         ((r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X2 @ X0))
% 7.52/7.74          | (r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X2 @ X0)))),
% 7.52/7.74      inference('sup-', [status(thm)], ['34', '37'])).
% 7.52/7.74  thf('39', plain,
% 7.52/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.52/7.74         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X2 @ X0))),
% 7.52/7.74      inference('simplify', [status(thm)], ['38'])).
% 7.52/7.74  thf('40', plain,
% 7.52/7.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 7.52/7.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.52/7.74  thf('41', plain,
% 7.52/7.74      (![X12 : $i, X13 : $i]:
% 7.52/7.74         ((r1_xboole_0 @ X12 @ X13)
% 7.52/7.74          | (r2_hidden @ (sk_C_1 @ X13 @ X12) @ (k3_xboole_0 @ X12 @ X13)))),
% 7.52/7.74      inference('cnf', [status(esa)], [t4_xboole_0])).
% 7.52/7.74  thf('42', plain,
% 7.52/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.52/7.74         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 7.52/7.74      inference('sup-', [status(thm)], ['30', '32'])).
% 7.52/7.74  thf('43', plain,
% 7.52/7.74      (![X0 : $i, X1 : $i]:
% 7.52/7.74         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X1))),
% 7.52/7.74      inference('sup-', [status(thm)], ['41', '42'])).
% 7.52/7.74  thf(d1_tarski, axiom,
% 7.52/7.74    (![A:$i,B:$i]:
% 7.52/7.74     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 7.52/7.74       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 7.52/7.74  thf('44', plain,
% 7.52/7.74      (![X18 : $i, X20 : $i, X21 : $i]:
% 7.52/7.74         (~ (r2_hidden @ X21 @ X20)
% 7.52/7.74          | ((X21) = (X18))
% 7.52/7.74          | ((X20) != (k1_tarski @ X18)))),
% 7.52/7.74      inference('cnf', [status(esa)], [d1_tarski])).
% 7.52/7.74  thf('45', plain,
% 7.52/7.74      (![X18 : $i, X21 : $i]:
% 7.52/7.74         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 7.52/7.74      inference('simplify', [status(thm)], ['44'])).
% 7.52/7.74  thf('46', plain,
% 7.52/7.74      (![X0 : $i, X1 : $i]:
% 7.52/7.74         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 7.52/7.74          | ((sk_C_1 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 7.52/7.74      inference('sup-', [status(thm)], ['43', '45'])).
% 7.52/7.74  thf('47', plain,
% 7.52/7.74      (![X12 : $i, X13 : $i]:
% 7.52/7.74         ((r1_xboole_0 @ X12 @ X13)
% 7.52/7.74          | (r2_hidden @ (sk_C_1 @ X13 @ X12) @ (k3_xboole_0 @ X12 @ X13)))),
% 7.52/7.74      inference('cnf', [status(esa)], [t4_xboole_0])).
% 7.52/7.74  thf('48', plain,
% 7.52/7.74      (![X8 : $i, X10 : $i, X11 : $i]:
% 7.52/7.74         (~ (r2_hidden @ X10 @ X8)
% 7.52/7.74          | ~ (r2_hidden @ X10 @ X11)
% 7.52/7.74          | ~ (r1_xboole_0 @ X8 @ X11))),
% 7.52/7.74      inference('cnf', [status(esa)], [t3_xboole_0])).
% 7.52/7.74  thf('49', plain,
% 7.52/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.52/7.74         ((r1_xboole_0 @ X1 @ X0)
% 7.52/7.74          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 7.52/7.74          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 7.52/7.74      inference('sup-', [status(thm)], ['47', '48'])).
% 7.52/7.74  thf('50', plain,
% 7.52/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.52/7.74         (~ (r2_hidden @ X0 @ X1)
% 7.52/7.74          | (r1_xboole_0 @ (k1_tarski @ X0) @ X2)
% 7.52/7.74          | ~ (r1_xboole_0 @ (k3_xboole_0 @ (k1_tarski @ X0) @ X2) @ X1)
% 7.52/7.74          | (r1_xboole_0 @ (k1_tarski @ X0) @ X2))),
% 7.52/7.74      inference('sup-', [status(thm)], ['46', '49'])).
% 7.52/7.74  thf('51', plain,
% 7.52/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.52/7.74         (~ (r1_xboole_0 @ (k3_xboole_0 @ (k1_tarski @ X0) @ X2) @ X1)
% 7.52/7.74          | (r1_xboole_0 @ (k1_tarski @ X0) @ X2)
% 7.52/7.74          | ~ (r2_hidden @ X0 @ X1))),
% 7.52/7.74      inference('simplify', [status(thm)], ['50'])).
% 7.52/7.74  thf('52', plain,
% 7.52/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.52/7.74         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0)) @ X2)
% 7.52/7.74          | ~ (r2_hidden @ X0 @ X2)
% 7.52/7.74          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 7.52/7.74      inference('sup-', [status(thm)], ['40', '51'])).
% 7.52/7.74  thf('53', plain,
% 7.52/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.52/7.74         ((r1_xboole_0 @ (k1_tarski @ X2) @ X0)
% 7.52/7.74          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 7.52/7.74      inference('sup-', [status(thm)], ['39', '52'])).
% 7.52/7.74  thf('54', plain,
% 7.52/7.74      (![X0 : $i]:
% 7.52/7.74         (r1_xboole_0 @ (k1_tarski @ sk_A) @ (k4_xboole_0 @ X0 @ sk_B))),
% 7.52/7.74      inference('sup-', [status(thm)], ['28', '53'])).
% 7.52/7.74  thf('55', plain,
% 7.52/7.74      (![X3 : $i, X4 : $i, X7 : $i]:
% 7.52/7.74         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 7.52/7.74          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 7.52/7.74          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 7.52/7.74      inference('cnf', [status(esa)], [d5_xboole_0])).
% 7.52/7.74  thf('56', plain,
% 7.52/7.74      (![X0 : $i, X1 : $i]:
% 7.52/7.74         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 7.52/7.74          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 7.52/7.74      inference('eq_fact', [status(thm)], ['55'])).
% 7.52/7.74  thf('57', plain,
% 7.52/7.74      (![X3 : $i, X4 : $i, X7 : $i]:
% 7.52/7.74         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 7.52/7.74          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 7.52/7.74          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 7.52/7.74          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 7.52/7.74      inference('cnf', [status(esa)], [d5_xboole_0])).
% 7.52/7.74  thf('58', plain,
% 7.52/7.74      (![X0 : $i, X1 : $i]:
% 7.52/7.74         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 7.52/7.74          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 7.52/7.74          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 7.52/7.74          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 7.52/7.74      inference('sup-', [status(thm)], ['56', '57'])).
% 7.52/7.74  thf('59', plain,
% 7.52/7.74      (![X0 : $i, X1 : $i]:
% 7.52/7.74         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 7.52/7.74          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 7.52/7.74          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 7.52/7.74      inference('simplify', [status(thm)], ['58'])).
% 7.52/7.74  thf('60', plain,
% 7.52/7.74      (![X0 : $i, X1 : $i]:
% 7.52/7.74         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 7.52/7.74          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 7.52/7.74      inference('eq_fact', [status(thm)], ['55'])).
% 7.52/7.74  thf('61', plain,
% 7.52/7.74      (![X0 : $i, X1 : $i]:
% 7.52/7.74         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 7.52/7.74          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 7.52/7.74      inference('clc', [status(thm)], ['59', '60'])).
% 7.52/7.74  thf('62', plain,
% 7.52/7.74      (![X0 : $i, X1 : $i]:
% 7.52/7.74         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 7.52/7.74          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 7.52/7.74      inference('eq_fact', [status(thm)], ['55'])).
% 7.52/7.74  thf('63', plain,
% 7.52/7.74      (![X8 : $i, X10 : $i, X11 : $i]:
% 7.52/7.74         (~ (r2_hidden @ X10 @ X8)
% 7.52/7.74          | ~ (r2_hidden @ X10 @ X11)
% 7.52/7.74          | ~ (r1_xboole_0 @ X8 @ X11))),
% 7.52/7.74      inference('cnf', [status(esa)], [t3_xboole_0])).
% 7.52/7.74  thf('64', plain,
% 7.52/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.52/7.74         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 7.52/7.74          | ~ (r1_xboole_0 @ X0 @ X2)
% 7.52/7.74          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X2))),
% 7.52/7.74      inference('sup-', [status(thm)], ['62', '63'])).
% 7.52/7.74  thf('65', plain,
% 7.52/7.74      (![X0 : $i, X1 : $i]:
% 7.52/7.74         (((X1) = (k4_xboole_0 @ X1 @ X0))
% 7.52/7.74          | ~ (r1_xboole_0 @ X1 @ X0)
% 7.52/7.74          | ((X1) = (k4_xboole_0 @ X1 @ X0)))),
% 7.52/7.74      inference('sup-', [status(thm)], ['61', '64'])).
% 7.52/7.74  thf('66', plain,
% 7.52/7.74      (![X0 : $i, X1 : $i]:
% 7.52/7.74         (~ (r1_xboole_0 @ X1 @ X0) | ((X1) = (k4_xboole_0 @ X1 @ X0)))),
% 7.52/7.74      inference('simplify', [status(thm)], ['65'])).
% 7.52/7.74  thf('67', plain,
% 7.52/7.74      (![X0 : $i]:
% 7.52/7.74         ((k1_tarski @ sk_A)
% 7.52/7.74           = (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k4_xboole_0 @ X0 @ sk_B)))),
% 7.52/7.74      inference('sup-', [status(thm)], ['54', '66'])).
% 7.52/7.74  thf('68', plain,
% 7.52/7.74      (((k1_tarski @ sk_A) = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 7.52/7.74      inference('sup+', [status(thm)], ['0', '67'])).
% 7.52/7.74  thf('69', plain,
% 7.52/7.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 7.52/7.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.52/7.74  thf('70', plain,
% 7.52/7.74      (((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 7.52/7.74      inference('demod', [status(thm)], ['68', '69'])).
% 7.52/7.74  thf('71', plain,
% 7.52/7.74      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (k1_tarski @ sk_A))),
% 7.52/7.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.52/7.74  thf('72', plain, ($false),
% 7.52/7.74      inference('simplify_reflect-', [status(thm)], ['70', '71'])).
% 7.52/7.74  
% 7.52/7.74  % SZS output end Refutation
% 7.52/7.74  
% 7.59/7.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
