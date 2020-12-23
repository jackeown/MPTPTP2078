%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cNce74XCry

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:35 EST 2020

% Result     : Theorem 1.09s
% Output     : Refutation 1.09s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 556 expanded)
%              Number of leaves         :   15 ( 156 expanded)
%              Depth                    :   24
%              Number of atoms          : 1207 (7045 expanded)
%              Number of equality atoms :   55 ( 351 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t120_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
         => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t120_relat_1])).

thf('4',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(t115_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k2_relat_1 @ ( k8_relat_1 @ B @ C ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ ( k2_relat_1 @ X17 ) )
      | ( r2_hidden @ X15 @ ( k2_relat_1 @ ( k8_relat_1 @ X16 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t115_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ sk_B ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ sk_B ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,
    ( ( r1_tarski @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k3_xboole_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D @ sk_A @ X0 @ sk_A ) @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['1','18'])).

thf('20',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('21',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_D @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) @ sk_A ) @ sk_A )
    | ( sk_A
      = ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) @ sk_A ) @ sk_A )
    | ( sk_A
      = ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('24',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('26',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('27',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X3 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X3 )
      | ( X3
        = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ X3 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ ( k3_xboole_0 @ X2 @ X0 ) @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('31',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('32',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) @ ( k3_xboole_0 @ X0 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['35'])).

thf('37',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['35'])).

thf('40',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['35'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['38','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('47',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','46','47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( r2_hidden @ ( sk_D @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ) @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) )
    | ( ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['24','50'])).

thf('52',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('53',plain,
    ( ( r2_hidden @ ( sk_D @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ) @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) )
    | ( ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) )
      = sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    r2_hidden @ ( sk_D @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ) @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

thf('56',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('57',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('58',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k2_relat_1 @ ( k8_relat_1 @ X16 @ X17 ) ) )
      | ( r2_hidden @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t115_relat_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('61',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) ) @ ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) ) @ ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ) @ sk_A )
      | ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('69',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) @ sk_A )
    | ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) @ sk_A ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    r2_hidden @ ( sk_D @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ) @ sk_A ),
    inference('sup-',[status(thm)],['55','72'])).

thf('74',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('75',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ) @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r2_hidden @ ( sk_D @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ) @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) )
    | ( ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    r2_hidden @ ( sk_D @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ) @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

thf('77',plain,(
    r2_hidden @ ( sk_D @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ) @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['35'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k3_xboole_0 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ sk_A @ sk_A @ X0 ) @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('82',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ( sk_A
      = ( k3_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( sk_A
    = ( k3_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['75','76','77','83'])).

thf('85',plain,(
    ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['84','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cNce74XCry
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:45:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.09/1.33  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.09/1.33  % Solved by: fo/fo7.sh
% 1.09/1.33  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.09/1.33  % done 1238 iterations in 0.871s
% 1.09/1.33  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.09/1.33  % SZS output start Refutation
% 1.09/1.33  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.09/1.33  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.09/1.33  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.09/1.33  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.09/1.33  thf(sk_A_type, type, sk_A: $i).
% 1.09/1.33  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.09/1.33  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 1.09/1.33  thf(sk_B_type, type, sk_B: $i).
% 1.09/1.33  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.09/1.33  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.09/1.33  thf(d4_xboole_0, axiom,
% 1.09/1.33    (![A:$i,B:$i,C:$i]:
% 1.09/1.33     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.09/1.33       ( ![D:$i]:
% 1.09/1.33         ( ( r2_hidden @ D @ C ) <=>
% 1.09/1.33           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.09/1.33  thf('0', plain,
% 1.09/1.33      (![X5 : $i, X6 : $i, X9 : $i]:
% 1.09/1.33         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 1.09/1.33          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 1.09/1.33          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 1.09/1.33      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.09/1.33  thf('1', plain,
% 1.09/1.33      (![X0 : $i, X1 : $i]:
% 1.09/1.33         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.09/1.33          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 1.09/1.33      inference('eq_fact', [status(thm)], ['0'])).
% 1.09/1.33  thf(d3_tarski, axiom,
% 1.09/1.33    (![A:$i,B:$i]:
% 1.09/1.33     ( ( r1_tarski @ A @ B ) <=>
% 1.09/1.33       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.09/1.33  thf('2', plain,
% 1.09/1.33      (![X1 : $i, X3 : $i]:
% 1.09/1.33         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.09/1.33      inference('cnf', [status(esa)], [d3_tarski])).
% 1.09/1.33  thf('3', plain,
% 1.09/1.33      (![X1 : $i, X3 : $i]:
% 1.09/1.33         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.09/1.33      inference('cnf', [status(esa)], [d3_tarski])).
% 1.09/1.33  thf(t120_relat_1, conjecture,
% 1.09/1.33    (![A:$i,B:$i]:
% 1.09/1.33     ( ( v1_relat_1 @ B ) =>
% 1.09/1.33       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 1.09/1.33         ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) = ( A ) ) ) ))).
% 1.09/1.33  thf(zf_stmt_0, negated_conjecture,
% 1.09/1.33    (~( ![A:$i,B:$i]:
% 1.09/1.33        ( ( v1_relat_1 @ B ) =>
% 1.09/1.33          ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 1.09/1.33            ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) = ( A ) ) ) ) )),
% 1.09/1.33    inference('cnf.neg', [status(esa)], [t120_relat_1])).
% 1.09/1.33  thf('4', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 1.09/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.33  thf('5', plain,
% 1.09/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.09/1.33         (~ (r2_hidden @ X0 @ X1)
% 1.09/1.33          | (r2_hidden @ X0 @ X2)
% 1.09/1.33          | ~ (r1_tarski @ X1 @ X2))),
% 1.09/1.33      inference('cnf', [status(esa)], [d3_tarski])).
% 1.09/1.33  thf('6', plain,
% 1.09/1.33      (![X0 : $i]:
% 1.09/1.33         ((r2_hidden @ X0 @ (k2_relat_1 @ sk_B)) | ~ (r2_hidden @ X0 @ sk_A))),
% 1.09/1.33      inference('sup-', [status(thm)], ['4', '5'])).
% 1.09/1.33  thf('7', plain,
% 1.09/1.33      (![X0 : $i]:
% 1.09/1.33         ((r1_tarski @ sk_A @ X0)
% 1.09/1.33          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 1.09/1.33      inference('sup-', [status(thm)], ['3', '6'])).
% 1.09/1.33  thf(t115_relat_1, axiom,
% 1.09/1.33    (![A:$i,B:$i,C:$i]:
% 1.09/1.33     ( ( v1_relat_1 @ C ) =>
% 1.09/1.33       ( ( r2_hidden @ A @ ( k2_relat_1 @ ( k8_relat_1 @ B @ C ) ) ) <=>
% 1.09/1.33         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ C ) ) ) ) ))).
% 1.09/1.33  thf('8', plain,
% 1.09/1.33      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.09/1.33         (~ (r2_hidden @ X15 @ X16)
% 1.09/1.33          | ~ (r2_hidden @ X15 @ (k2_relat_1 @ X17))
% 1.09/1.33          | (r2_hidden @ X15 @ (k2_relat_1 @ (k8_relat_1 @ X16 @ X17)))
% 1.09/1.33          | ~ (v1_relat_1 @ X17))),
% 1.09/1.33      inference('cnf', [status(esa)], [t115_relat_1])).
% 1.09/1.33  thf('9', plain,
% 1.09/1.33      (![X0 : $i, X1 : $i]:
% 1.09/1.33         ((r1_tarski @ sk_A @ X0)
% 1.09/1.33          | ~ (v1_relat_1 @ sk_B)
% 1.09/1.33          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ 
% 1.09/1.33             (k2_relat_1 @ (k8_relat_1 @ X1 @ sk_B)))
% 1.09/1.33          | ~ (r2_hidden @ (sk_C @ X0 @ sk_A) @ X1))),
% 1.09/1.33      inference('sup-', [status(thm)], ['7', '8'])).
% 1.09/1.33  thf('10', plain, ((v1_relat_1 @ sk_B)),
% 1.09/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.33  thf('11', plain,
% 1.09/1.33      (![X0 : $i, X1 : $i]:
% 1.09/1.33         ((r1_tarski @ sk_A @ X0)
% 1.09/1.33          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ 
% 1.09/1.33             (k2_relat_1 @ (k8_relat_1 @ X1 @ sk_B)))
% 1.09/1.33          | ~ (r2_hidden @ (sk_C @ X0 @ sk_A) @ X1))),
% 1.09/1.33      inference('demod', [status(thm)], ['9', '10'])).
% 1.09/1.33  thf('12', plain,
% 1.09/1.33      (![X0 : $i]:
% 1.09/1.33         ((r1_tarski @ sk_A @ X0)
% 1.09/1.33          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ 
% 1.09/1.33             (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)))
% 1.09/1.33          | (r1_tarski @ sk_A @ X0))),
% 1.09/1.33      inference('sup-', [status(thm)], ['2', '11'])).
% 1.09/1.33  thf('13', plain,
% 1.09/1.33      (![X0 : $i]:
% 1.09/1.33         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ 
% 1.09/1.33           (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)))
% 1.09/1.33          | (r1_tarski @ sk_A @ X0))),
% 1.09/1.33      inference('simplify', [status(thm)], ['12'])).
% 1.09/1.33  thf('14', plain,
% 1.09/1.33      (![X1 : $i, X3 : $i]:
% 1.09/1.33         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.09/1.33      inference('cnf', [status(esa)], [d3_tarski])).
% 1.09/1.33  thf('15', plain,
% 1.09/1.33      (((r1_tarski @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)))
% 1.09/1.33        | (r1_tarski @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B))))),
% 1.09/1.33      inference('sup-', [status(thm)], ['13', '14'])).
% 1.09/1.33  thf('16', plain,
% 1.09/1.33      ((r1_tarski @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)))),
% 1.09/1.33      inference('simplify', [status(thm)], ['15'])).
% 1.09/1.33  thf('17', plain,
% 1.09/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.09/1.33         (~ (r2_hidden @ X0 @ X1)
% 1.09/1.33          | (r2_hidden @ X0 @ X2)
% 1.09/1.33          | ~ (r1_tarski @ X1 @ X2))),
% 1.09/1.33      inference('cnf', [status(esa)], [d3_tarski])).
% 1.09/1.33  thf('18', plain,
% 1.09/1.33      (![X0 : $i]:
% 1.09/1.33         ((r2_hidden @ X0 @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)))
% 1.09/1.33          | ~ (r2_hidden @ X0 @ sk_A))),
% 1.09/1.33      inference('sup-', [status(thm)], ['16', '17'])).
% 1.09/1.33  thf('19', plain,
% 1.09/1.33      (![X0 : $i]:
% 1.09/1.33         (((sk_A) = (k3_xboole_0 @ sk_A @ X0))
% 1.09/1.33          | (r2_hidden @ (sk_D @ sk_A @ X0 @ sk_A) @ 
% 1.09/1.33             (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B))))),
% 1.09/1.33      inference('sup-', [status(thm)], ['1', '18'])).
% 1.09/1.33  thf('20', plain,
% 1.09/1.33      (![X5 : $i, X6 : $i, X9 : $i]:
% 1.09/1.33         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 1.09/1.33          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 1.09/1.33          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 1.09/1.33          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 1.09/1.33      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.09/1.33  thf('21', plain,
% 1.09/1.33      ((((sk_A)
% 1.09/1.33          = (k3_xboole_0 @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B))))
% 1.09/1.33        | ~ (r2_hidden @ 
% 1.09/1.33             (sk_D @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) @ sk_A) @ 
% 1.09/1.33             sk_A)
% 1.09/1.33        | ~ (r2_hidden @ 
% 1.09/1.33             (sk_D @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) @ sk_A) @ 
% 1.09/1.33             sk_A)
% 1.09/1.33        | ((sk_A)
% 1.09/1.33            = (k3_xboole_0 @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)))))),
% 1.09/1.33      inference('sup-', [status(thm)], ['19', '20'])).
% 1.09/1.33  thf('22', plain,
% 1.09/1.33      ((~ (r2_hidden @ 
% 1.09/1.33           (sk_D @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) @ sk_A) @ 
% 1.09/1.33           sk_A)
% 1.09/1.33        | ((sk_A)
% 1.09/1.33            = (k3_xboole_0 @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)))))),
% 1.09/1.33      inference('simplify', [status(thm)], ['21'])).
% 1.09/1.33  thf('23', plain,
% 1.09/1.33      (![X0 : $i, X1 : $i]:
% 1.09/1.33         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.09/1.33          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 1.09/1.33      inference('eq_fact', [status(thm)], ['0'])).
% 1.09/1.33  thf('24', plain,
% 1.09/1.33      (((sk_A)
% 1.09/1.33         = (k3_xboole_0 @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B))))),
% 1.09/1.33      inference('clc', [status(thm)], ['22', '23'])).
% 1.09/1.33  thf('25', plain,
% 1.09/1.33      (![X5 : $i, X6 : $i, X9 : $i]:
% 1.09/1.33         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 1.09/1.33          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 1.09/1.33          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 1.09/1.33      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.09/1.33  thf('26', plain,
% 1.09/1.33      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.09/1.33         (~ (r2_hidden @ X8 @ X7)
% 1.09/1.33          | (r2_hidden @ X8 @ X6)
% 1.09/1.33          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 1.09/1.33      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.09/1.33  thf('27', plain,
% 1.09/1.33      (![X5 : $i, X6 : $i, X8 : $i]:
% 1.09/1.33         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.09/1.33      inference('simplify', [status(thm)], ['26'])).
% 1.09/1.33  thf('28', plain,
% 1.09/1.33      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.09/1.33         ((r2_hidden @ (sk_D @ X3 @ (k3_xboole_0 @ X1 @ X0) @ X2) @ X3)
% 1.09/1.33          | ((X3) = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 1.09/1.33          | (r2_hidden @ (sk_D @ X3 @ (k3_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 1.09/1.33      inference('sup-', [status(thm)], ['25', '27'])).
% 1.09/1.33  thf('29', plain,
% 1.09/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.09/1.33         ((r2_hidden @ (sk_D @ X0 @ (k3_xboole_0 @ X2 @ X0) @ X1) @ X0)
% 1.09/1.33          | ((X0) = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0))))),
% 1.09/1.33      inference('eq_fact', [status(thm)], ['28'])).
% 1.09/1.33  thf('30', plain,
% 1.09/1.33      (![X0 : $i, X1 : $i]:
% 1.09/1.33         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.09/1.33          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 1.09/1.33      inference('eq_fact', [status(thm)], ['0'])).
% 1.09/1.33  thf('31', plain,
% 1.09/1.33      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.09/1.33         (~ (r2_hidden @ X4 @ X5)
% 1.09/1.33          | ~ (r2_hidden @ X4 @ X6)
% 1.09/1.33          | (r2_hidden @ X4 @ X7)
% 1.09/1.33          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 1.09/1.33      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.09/1.33  thf('32', plain,
% 1.09/1.33      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.09/1.33         ((r2_hidden @ X4 @ (k3_xboole_0 @ X5 @ X6))
% 1.09/1.33          | ~ (r2_hidden @ X4 @ X6)
% 1.09/1.33          | ~ (r2_hidden @ X4 @ X5))),
% 1.09/1.33      inference('simplify', [status(thm)], ['31'])).
% 1.09/1.33  thf('33', plain,
% 1.09/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.09/1.33         (((X0) = (k3_xboole_0 @ X0 @ X1))
% 1.09/1.33          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X2)
% 1.09/1.33          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X0)))),
% 1.09/1.33      inference('sup-', [status(thm)], ['30', '32'])).
% 1.09/1.33  thf('34', plain,
% 1.09/1.33      (![X0 : $i, X1 : $i]:
% 1.09/1.33         (((X0) = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 1.09/1.33          | (r2_hidden @ (sk_D @ X0 @ (k3_xboole_0 @ X1 @ X0) @ X0) @ 
% 1.09/1.33             (k3_xboole_0 @ X0 @ X0))
% 1.09/1.33          | ((X0) = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 1.09/1.33      inference('sup-', [status(thm)], ['29', '33'])).
% 1.09/1.33  thf('35', plain,
% 1.09/1.33      (![X5 : $i, X6 : $i, X9 : $i]:
% 1.09/1.33         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 1.09/1.33          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 1.09/1.33          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 1.09/1.33      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.09/1.33  thf('36', plain,
% 1.09/1.33      (![X0 : $i, X1 : $i]:
% 1.09/1.33         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.09/1.33          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.09/1.33      inference('eq_fact', [status(thm)], ['35'])).
% 1.09/1.33  thf('37', plain,
% 1.09/1.33      (![X5 : $i, X6 : $i, X8 : $i]:
% 1.09/1.33         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.09/1.33      inference('simplify', [status(thm)], ['26'])).
% 1.09/1.33  thf('38', plain,
% 1.09/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.09/1.33         (((k3_xboole_0 @ X1 @ X0)
% 1.09/1.33            = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 1.09/1.33          | (r2_hidden @ 
% 1.09/1.33             (sk_D @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0) @ X2) @ 
% 1.09/1.33             X0))),
% 1.09/1.33      inference('sup-', [status(thm)], ['36', '37'])).
% 1.09/1.33  thf('39', plain,
% 1.09/1.33      (![X0 : $i, X1 : $i]:
% 1.09/1.33         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.09/1.33          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.09/1.33      inference('eq_fact', [status(thm)], ['35'])).
% 1.09/1.33  thf('40', plain,
% 1.09/1.33      (![X5 : $i, X6 : $i, X9 : $i]:
% 1.09/1.33         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 1.09/1.33          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 1.09/1.33          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 1.09/1.33          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 1.09/1.33      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.09/1.33  thf('41', plain,
% 1.09/1.33      (![X0 : $i, X1 : $i]:
% 1.09/1.33         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 1.09/1.33          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.09/1.33          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.09/1.33          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.09/1.33      inference('sup-', [status(thm)], ['39', '40'])).
% 1.09/1.33  thf('42', plain,
% 1.09/1.33      (![X0 : $i, X1 : $i]:
% 1.09/1.33         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.09/1.33          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.09/1.33          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.09/1.33      inference('simplify', [status(thm)], ['41'])).
% 1.09/1.33  thf('43', plain,
% 1.09/1.33      (![X0 : $i, X1 : $i]:
% 1.09/1.33         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.09/1.33          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.09/1.33      inference('eq_fact', [status(thm)], ['35'])).
% 1.09/1.33  thf('44', plain,
% 1.09/1.33      (![X0 : $i, X1 : $i]:
% 1.09/1.33         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 1.09/1.33          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 1.09/1.33      inference('clc', [status(thm)], ['42', '43'])).
% 1.09/1.33  thf('45', plain,
% 1.09/1.33      (![X0 : $i, X1 : $i]:
% 1.09/1.33         (((k3_xboole_0 @ X1 @ X0)
% 1.09/1.33            = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 1.09/1.33          | ((k3_xboole_0 @ X1 @ X0)
% 1.09/1.33              = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 1.09/1.33      inference('sup-', [status(thm)], ['38', '44'])).
% 1.09/1.33  thf('46', plain,
% 1.09/1.33      (![X0 : $i, X1 : $i]:
% 1.09/1.33         ((k3_xboole_0 @ X1 @ X0)
% 1.09/1.33           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.09/1.33      inference('simplify', [status(thm)], ['45'])).
% 1.09/1.33  thf(idempotence_k3_xboole_0, axiom,
% 1.09/1.33    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.09/1.33  thf('47', plain, (![X10 : $i]: ((k3_xboole_0 @ X10 @ X10) = (X10))),
% 1.09/1.33      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.09/1.33  thf('48', plain,
% 1.09/1.33      (![X0 : $i, X1 : $i]:
% 1.09/1.33         ((k3_xboole_0 @ X1 @ X0)
% 1.09/1.33           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.09/1.33      inference('simplify', [status(thm)], ['45'])).
% 1.09/1.33  thf('49', plain,
% 1.09/1.33      (![X0 : $i, X1 : $i]:
% 1.09/1.33         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 1.09/1.33          | (r2_hidden @ (sk_D @ X0 @ (k3_xboole_0 @ X1 @ X0) @ X0) @ X0)
% 1.09/1.33          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.09/1.33      inference('demod', [status(thm)], ['34', '46', '47', '48'])).
% 1.09/1.33  thf('50', plain,
% 1.09/1.33      (![X0 : $i, X1 : $i]:
% 1.09/1.33         ((r2_hidden @ (sk_D @ X0 @ (k3_xboole_0 @ X1 @ X0) @ X0) @ X0)
% 1.09/1.33          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.09/1.33      inference('simplify', [status(thm)], ['49'])).
% 1.09/1.33  thf('51', plain,
% 1.09/1.33      (((r2_hidden @ 
% 1.09/1.33         (sk_D @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) @ sk_A @ 
% 1.09/1.33          (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B))) @ 
% 1.09/1.33         (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)))
% 1.09/1.33        | ((k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B))
% 1.09/1.33            = (k3_xboole_0 @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)))))),
% 1.09/1.33      inference('sup+', [status(thm)], ['24', '50'])).
% 1.09/1.33  thf('52', plain,
% 1.09/1.33      (((sk_A)
% 1.09/1.33         = (k3_xboole_0 @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B))))),
% 1.09/1.33      inference('clc', [status(thm)], ['22', '23'])).
% 1.09/1.33  thf('53', plain,
% 1.09/1.33      (((r2_hidden @ 
% 1.09/1.33         (sk_D @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) @ sk_A @ 
% 1.09/1.33          (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B))) @ 
% 1.09/1.33         (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)))
% 1.09/1.33        | ((k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) = (sk_A)))),
% 1.09/1.33      inference('demod', [status(thm)], ['51', '52'])).
% 1.09/1.33  thf('54', plain, (((k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) != (sk_A))),
% 1.09/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.33  thf('55', plain,
% 1.09/1.33      ((r2_hidden @ 
% 1.09/1.33        (sk_D @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) @ sk_A @ 
% 1.09/1.33         (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B))) @ 
% 1.09/1.33        (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)))),
% 1.09/1.33      inference('simplify_reflect-', [status(thm)], ['53', '54'])).
% 1.09/1.33  thf('56', plain,
% 1.09/1.33      (((sk_A)
% 1.09/1.33         = (k3_xboole_0 @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B))))),
% 1.09/1.33      inference('clc', [status(thm)], ['22', '23'])).
% 1.09/1.33  thf('57', plain,
% 1.09/1.33      (![X1 : $i, X3 : $i]:
% 1.09/1.33         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.09/1.33      inference('cnf', [status(esa)], [d3_tarski])).
% 1.09/1.33  thf('58', plain,
% 1.09/1.33      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.09/1.33         (~ (r2_hidden @ X15 @ (k2_relat_1 @ (k8_relat_1 @ X16 @ X17)))
% 1.09/1.33          | (r2_hidden @ X15 @ X16)
% 1.09/1.33          | ~ (v1_relat_1 @ X17))),
% 1.09/1.33      inference('cnf', [status(esa)], [t115_relat_1])).
% 1.09/1.33  thf('59', plain,
% 1.09/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.09/1.33         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X2)
% 1.09/1.33          | ~ (v1_relat_1 @ X0)
% 1.09/1.33          | (r2_hidden @ (sk_C @ X2 @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0))) @ 
% 1.09/1.33             X1))),
% 1.09/1.33      inference('sup-', [status(thm)], ['57', '58'])).
% 1.09/1.33  thf('60', plain,
% 1.09/1.33      (![X1 : $i, X3 : $i]:
% 1.09/1.33         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.09/1.33      inference('cnf', [status(esa)], [d3_tarski])).
% 1.09/1.33  thf('61', plain,
% 1.09/1.33      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.09/1.33         ((r2_hidden @ X4 @ (k3_xboole_0 @ X5 @ X6))
% 1.09/1.33          | ~ (r2_hidden @ X4 @ X6)
% 1.09/1.33          | ~ (r2_hidden @ X4 @ X5))),
% 1.09/1.33      inference('simplify', [status(thm)], ['31'])).
% 1.09/1.33  thf('62', plain,
% 1.09/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.09/1.33         ((r1_tarski @ X0 @ X1)
% 1.09/1.33          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 1.09/1.33          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X0)))),
% 1.09/1.33      inference('sup-', [status(thm)], ['60', '61'])).
% 1.09/1.33  thf('63', plain,
% 1.09/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.09/1.33         (~ (v1_relat_1 @ X1)
% 1.09/1.33          | (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ X1)) @ X2)
% 1.09/1.33          | (r2_hidden @ (sk_C @ X2 @ (k2_relat_1 @ (k8_relat_1 @ X0 @ X1))) @ 
% 1.09/1.33             (k3_xboole_0 @ X0 @ (k2_relat_1 @ (k8_relat_1 @ X0 @ X1))))
% 1.09/1.33          | (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ X1)) @ X2))),
% 1.09/1.33      inference('sup-', [status(thm)], ['59', '62'])).
% 1.09/1.33  thf('64', plain,
% 1.09/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.09/1.33         ((r2_hidden @ (sk_C @ X2 @ (k2_relat_1 @ (k8_relat_1 @ X0 @ X1))) @ 
% 1.09/1.33           (k3_xboole_0 @ X0 @ (k2_relat_1 @ (k8_relat_1 @ X0 @ X1))))
% 1.09/1.33          | (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ X1)) @ X2)
% 1.09/1.33          | ~ (v1_relat_1 @ X1))),
% 1.09/1.33      inference('simplify', [status(thm)], ['63'])).
% 1.09/1.33  thf('65', plain,
% 1.09/1.33      (![X0 : $i]:
% 1.09/1.33         ((r2_hidden @ 
% 1.09/1.33           (sk_C @ X0 @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B))) @ sk_A)
% 1.09/1.33          | ~ (v1_relat_1 @ sk_B)
% 1.09/1.33          | (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) @ X0))),
% 1.09/1.33      inference('sup+', [status(thm)], ['56', '64'])).
% 1.09/1.33  thf('66', plain, ((v1_relat_1 @ sk_B)),
% 1.09/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.33  thf('67', plain,
% 1.09/1.33      (![X0 : $i]:
% 1.09/1.33         ((r2_hidden @ 
% 1.09/1.33           (sk_C @ X0 @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B))) @ sk_A)
% 1.09/1.33          | (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) @ X0))),
% 1.09/1.33      inference('demod', [status(thm)], ['65', '66'])).
% 1.09/1.33  thf('68', plain,
% 1.09/1.33      (![X1 : $i, X3 : $i]:
% 1.09/1.33         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.09/1.33      inference('cnf', [status(esa)], [d3_tarski])).
% 1.09/1.33  thf('69', plain,
% 1.09/1.33      (((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) @ sk_A)
% 1.09/1.33        | (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) @ sk_A))),
% 1.09/1.33      inference('sup-', [status(thm)], ['67', '68'])).
% 1.09/1.33  thf('70', plain,
% 1.09/1.33      ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) @ sk_A)),
% 1.09/1.33      inference('simplify', [status(thm)], ['69'])).
% 1.09/1.33  thf('71', plain,
% 1.09/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.09/1.33         (~ (r2_hidden @ X0 @ X1)
% 1.09/1.33          | (r2_hidden @ X0 @ X2)
% 1.09/1.33          | ~ (r1_tarski @ X1 @ X2))),
% 1.09/1.33      inference('cnf', [status(esa)], [d3_tarski])).
% 1.09/1.33  thf('72', plain,
% 1.09/1.33      (![X0 : $i]:
% 1.09/1.33         ((r2_hidden @ X0 @ sk_A)
% 1.09/1.33          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B))))),
% 1.09/1.33      inference('sup-', [status(thm)], ['70', '71'])).
% 1.09/1.33  thf('73', plain,
% 1.09/1.33      ((r2_hidden @ 
% 1.09/1.33        (sk_D @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) @ sk_A @ 
% 1.09/1.33         (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B))) @ 
% 1.09/1.33        sk_A)),
% 1.09/1.33      inference('sup-', [status(thm)], ['55', '72'])).
% 1.09/1.33  thf('74', plain,
% 1.09/1.33      (![X5 : $i, X6 : $i, X9 : $i]:
% 1.09/1.33         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 1.09/1.33          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 1.09/1.33          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 1.09/1.33          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 1.09/1.33      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.09/1.33  thf('75', plain,
% 1.09/1.33      ((~ (r2_hidden @ 
% 1.09/1.33           (sk_D @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) @ sk_A @ 
% 1.09/1.33            (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B))) @ 
% 1.09/1.33           (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)))
% 1.09/1.33        | ~ (r2_hidden @ 
% 1.09/1.33             (sk_D @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) @ sk_A @ 
% 1.09/1.33              (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B))) @ 
% 1.09/1.33             (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)))
% 1.09/1.33        | ((k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B))
% 1.09/1.33            = (k3_xboole_0 @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) @ sk_A)))),
% 1.09/1.33      inference('sup-', [status(thm)], ['73', '74'])).
% 1.09/1.33  thf('76', plain,
% 1.09/1.33      ((r2_hidden @ 
% 1.09/1.33        (sk_D @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) @ sk_A @ 
% 1.09/1.33         (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B))) @ 
% 1.09/1.33        (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)))),
% 1.09/1.33      inference('simplify_reflect-', [status(thm)], ['53', '54'])).
% 1.09/1.33  thf('77', plain,
% 1.09/1.33      ((r2_hidden @ 
% 1.09/1.33        (sk_D @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) @ sk_A @ 
% 1.09/1.33         (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B))) @ 
% 1.09/1.33        (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)))),
% 1.09/1.33      inference('simplify_reflect-', [status(thm)], ['53', '54'])).
% 1.09/1.33  thf('78', plain,
% 1.09/1.33      (![X0 : $i, X1 : $i]:
% 1.09/1.33         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.09/1.33          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.09/1.33      inference('eq_fact', [status(thm)], ['35'])).
% 1.09/1.33  thf('79', plain,
% 1.09/1.33      (![X0 : $i]:
% 1.09/1.33         ((r2_hidden @ X0 @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)))
% 1.09/1.33          | ~ (r2_hidden @ X0 @ sk_A))),
% 1.09/1.33      inference('sup-', [status(thm)], ['16', '17'])).
% 1.09/1.33  thf('80', plain,
% 1.09/1.33      (![X0 : $i]:
% 1.09/1.33         (((sk_A) = (k3_xboole_0 @ X0 @ sk_A))
% 1.09/1.33          | (r2_hidden @ (sk_D @ sk_A @ sk_A @ X0) @ 
% 1.09/1.33             (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B))))),
% 1.09/1.33      inference('sup-', [status(thm)], ['78', '79'])).
% 1.09/1.33  thf('81', plain,
% 1.09/1.33      (![X0 : $i, X1 : $i]:
% 1.09/1.33         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 1.09/1.33          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 1.09/1.33      inference('clc', [status(thm)], ['42', '43'])).
% 1.09/1.33  thf('82', plain,
% 1.09/1.33      ((((sk_A)
% 1.09/1.33          = (k3_xboole_0 @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) @ sk_A))
% 1.09/1.33        | ((sk_A)
% 1.09/1.33            = (k3_xboole_0 @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) @ sk_A)))),
% 1.09/1.33      inference('sup-', [status(thm)], ['80', '81'])).
% 1.09/1.33  thf('83', plain,
% 1.09/1.33      (((sk_A)
% 1.09/1.33         = (k3_xboole_0 @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) @ sk_A))),
% 1.09/1.33      inference('simplify', [status(thm)], ['82'])).
% 1.09/1.33  thf('84', plain, (((k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) = (sk_A))),
% 1.09/1.33      inference('demod', [status(thm)], ['75', '76', '77', '83'])).
% 1.09/1.33  thf('85', plain, (((k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) != (sk_A))),
% 1.09/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.33  thf('86', plain, ($false),
% 1.09/1.33      inference('simplify_reflect-', [status(thm)], ['84', '85'])).
% 1.09/1.33  
% 1.09/1.33  % SZS output end Refutation
% 1.09/1.33  
% 1.20/1.34  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
