%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jPY1zvbXcx

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:15 EST 2020

% Result     : Theorem 2.82s
% Output     : Refutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 238 expanded)
%              Number of leaves         :   24 (  85 expanded)
%              Depth                    :   21
%              Number of atoms          :  952 (1833 expanded)
%              Number of equality atoms :   94 ( 205 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t48_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t48_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k4_xboole_0 @ X29 @ ( k3_xboole_0 @ X29 @ X30 ) )
      = ( k4_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X24 ) )
      = ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('8',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k3_xboole_0 @ X19 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k4_xboole_0 @ X29 @ ( k3_xboole_0 @ X29 @ X30 ) )
      = ( k4_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X22: $i] :
      ( ( k2_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X27 @ X28 ) @ X28 )
      = ( k4_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X23: $i] :
      ( ( k3_xboole_0 @ X23 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k4_xboole_0 @ X29 @ ( k3_xboole_0 @ X29 @ X30 ) )
      = ( k4_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('25',plain,(
    ! [X26: $i] :
      ( ( k4_xboole_0 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['14','27'])).

thf('29',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X24 ) )
      = ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X22: $i] :
      ( ( k2_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['7','32'])).

thf('34',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X24 ) )
      = ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('35',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X27 @ X28 ) @ X28 )
      = ( k4_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('37',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('38',plain,(
    ! [X26: $i] :
      ( ( k4_xboole_0 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('39',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('40',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

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

thf('46',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('47',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('48',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('53',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('54',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k3_xboole_0 @ X15 @ X18 ) )
      | ~ ( r1_xboole_0 @ X15 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('59',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X27 @ X28 ) @ X28 )
      = ( k4_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('60',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X24 ) )
      = ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X24 ) )
      = ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','63'])).

thf('65',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X27 @ X28 ) @ X28 )
      = ( k4_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','26'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['7','32'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k3_xboole_0 @ X15 @ X18 ) )
      | ~ ( r1_xboole_0 @ X15 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['57','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','76'])).

thf('78',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k4_xboole_0 @ X29 @ ( k3_xboole_0 @ X29 @ X30 ) )
      = ( k4_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X26: $i] :
      ( ( k4_xboole_0 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['36','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','82'])).

thf('84',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k4_xboole_0 @ X29 @ ( k3_xboole_0 @ X29 @ X30 ) )
      = ( k4_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('85',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X24 ) )
      = ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('87',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X27 @ X28 ) @ X28 )
      = ( k4_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['84','91'])).

thf('93',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k4_xboole_0 @ X29 @ ( k3_xboole_0 @ X29 @ X30 ) )
      = ( k4_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['83','94'])).

thf('96',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('97',plain,(
    ( k3_xboole_0 @ sk_B @ sk_A )
 != ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['2','95','96'])).

thf('98',plain,(
    $false ),
    inference(simplify,[status(thm)],['97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jPY1zvbXcx
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:37:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.82/3.02  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.82/3.02  % Solved by: fo/fo7.sh
% 2.82/3.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.82/3.02  % done 2192 iterations in 2.517s
% 2.82/3.02  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.82/3.02  % SZS output start Refutation
% 2.82/3.02  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.82/3.02  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.82/3.02  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.82/3.02  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.82/3.02  thf(sk_B_type, type, sk_B: $i).
% 2.82/3.02  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.82/3.02  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.82/3.02  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.82/3.02  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.82/3.02  thf(sk_A_type, type, sk_A: $i).
% 2.82/3.02  thf(t48_xboole_1, conjecture,
% 2.82/3.02    (![A:$i,B:$i]:
% 2.82/3.02     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.82/3.02  thf(zf_stmt_0, negated_conjecture,
% 2.82/3.02    (~( ![A:$i,B:$i]:
% 2.82/3.02        ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) =
% 2.82/3.02          ( k3_xboole_0 @ A @ B ) ) )),
% 2.82/3.02    inference('cnf.neg', [status(esa)], [t48_xboole_1])).
% 2.82/3.02  thf('0', plain,
% 2.82/3.02      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 2.82/3.02         != (k3_xboole_0 @ sk_A @ sk_B))),
% 2.82/3.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.02  thf(commutativity_k3_xboole_0, axiom,
% 2.82/3.02    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.82/3.02  thf('1', plain,
% 2.82/3.02      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.82/3.02      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.82/3.02  thf('2', plain,
% 2.82/3.02      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 2.82/3.02         != (k3_xboole_0 @ sk_B @ sk_A))),
% 2.82/3.02      inference('demod', [status(thm)], ['0', '1'])).
% 2.82/3.02  thf(t47_xboole_1, axiom,
% 2.82/3.02    (![A:$i,B:$i]:
% 2.82/3.02     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 2.82/3.02  thf('3', plain,
% 2.82/3.02      (![X29 : $i, X30 : $i]:
% 2.82/3.02         ((k4_xboole_0 @ X29 @ (k3_xboole_0 @ X29 @ X30))
% 2.82/3.02           = (k4_xboole_0 @ X29 @ X30))),
% 2.82/3.02      inference('cnf', [status(esa)], [t47_xboole_1])).
% 2.82/3.02  thf(t39_xboole_1, axiom,
% 2.82/3.02    (![A:$i,B:$i]:
% 2.82/3.02     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.82/3.02  thf('4', plain,
% 2.82/3.02      (![X24 : $i, X25 : $i]:
% 2.82/3.02         ((k2_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X24))
% 2.82/3.02           = (k2_xboole_0 @ X24 @ X25))),
% 2.82/3.02      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.82/3.02  thf('5', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 2.82/3.02           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 2.82/3.02      inference('sup+', [status(thm)], ['3', '4'])).
% 2.82/3.02  thf(commutativity_k2_xboole_0, axiom,
% 2.82/3.02    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.82/3.02  thf('6', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.82/3.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.82/3.02  thf('7', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 2.82/3.02           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.82/3.02      inference('demod', [status(thm)], ['5', '6'])).
% 2.82/3.02  thf(idempotence_k3_xboole_0, axiom,
% 2.82/3.02    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 2.82/3.02  thf('8', plain, (![X10 : $i]: ((k3_xboole_0 @ X10 @ X10) = (X10))),
% 2.82/3.02      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 2.82/3.02  thf(t16_xboole_1, axiom,
% 2.82/3.02    (![A:$i,B:$i,C:$i]:
% 2.82/3.02     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 2.82/3.02       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 2.82/3.02  thf('9', plain,
% 2.82/3.02      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.82/3.02         ((k3_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ X21)
% 2.82/3.02           = (k3_xboole_0 @ X19 @ (k3_xboole_0 @ X20 @ X21)))),
% 2.82/3.02      inference('cnf', [status(esa)], [t16_xboole_1])).
% 2.82/3.02  thf('10', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((k3_xboole_0 @ X0 @ X1)
% 2.82/3.02           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.82/3.02      inference('sup+', [status(thm)], ['8', '9'])).
% 2.82/3.02  thf('11', plain,
% 2.82/3.02      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.82/3.02      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.82/3.02  thf('12', plain,
% 2.82/3.02      (![X29 : $i, X30 : $i]:
% 2.82/3.02         ((k4_xboole_0 @ X29 @ (k3_xboole_0 @ X29 @ X30))
% 2.82/3.02           = (k4_xboole_0 @ X29 @ X30))),
% 2.82/3.02      inference('cnf', [status(esa)], [t47_xboole_1])).
% 2.82/3.02  thf('13', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 2.82/3.02           = (k4_xboole_0 @ X0 @ X1))),
% 2.82/3.02      inference('sup+', [status(thm)], ['11', '12'])).
% 2.82/3.02  thf('14', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 2.82/3.02           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 2.82/3.02      inference('sup+', [status(thm)], ['10', '13'])).
% 2.82/3.02  thf('15', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.82/3.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.82/3.02  thf(t1_boole, axiom,
% 2.82/3.02    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.82/3.02  thf('16', plain, (![X22 : $i]: ((k2_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 2.82/3.02      inference('cnf', [status(esa)], [t1_boole])).
% 2.82/3.02  thf('17', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.82/3.02      inference('sup+', [status(thm)], ['15', '16'])).
% 2.82/3.02  thf(t40_xboole_1, axiom,
% 2.82/3.02    (![A:$i,B:$i]:
% 2.82/3.02     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 2.82/3.02  thf('18', plain,
% 2.82/3.02      (![X27 : $i, X28 : $i]:
% 2.82/3.02         ((k4_xboole_0 @ (k2_xboole_0 @ X27 @ X28) @ X28)
% 2.82/3.02           = (k4_xboole_0 @ X27 @ X28))),
% 2.82/3.02      inference('cnf', [status(esa)], [t40_xboole_1])).
% 2.82/3.02  thf('19', plain,
% 2.82/3.02      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 2.82/3.02      inference('sup+', [status(thm)], ['17', '18'])).
% 2.82/3.02  thf('20', plain,
% 2.82/3.02      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.82/3.02      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.82/3.02  thf(t2_boole, axiom,
% 2.82/3.02    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 2.82/3.02  thf('21', plain,
% 2.82/3.02      (![X23 : $i]: ((k3_xboole_0 @ X23 @ k1_xboole_0) = (k1_xboole_0))),
% 2.82/3.02      inference('cnf', [status(esa)], [t2_boole])).
% 2.82/3.02  thf('22', plain,
% 2.82/3.02      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.82/3.02      inference('sup+', [status(thm)], ['20', '21'])).
% 2.82/3.02  thf('23', plain,
% 2.82/3.02      (![X29 : $i, X30 : $i]:
% 2.82/3.02         ((k4_xboole_0 @ X29 @ (k3_xboole_0 @ X29 @ X30))
% 2.82/3.02           = (k4_xboole_0 @ X29 @ X30))),
% 2.82/3.02      inference('cnf', [status(esa)], [t47_xboole_1])).
% 2.82/3.02  thf('24', plain,
% 2.82/3.02      (![X0 : $i]:
% 2.82/3.02         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 2.82/3.02           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 2.82/3.02      inference('sup+', [status(thm)], ['22', '23'])).
% 2.82/3.02  thf(t3_boole, axiom,
% 2.82/3.02    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.82/3.02  thf('25', plain, (![X26 : $i]: ((k4_xboole_0 @ X26 @ k1_xboole_0) = (X26))),
% 2.82/3.02      inference('cnf', [status(esa)], [t3_boole])).
% 2.82/3.02  thf('26', plain,
% 2.82/3.02      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 2.82/3.02      inference('demod', [status(thm)], ['24', '25'])).
% 2.82/3.02  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.82/3.02      inference('demod', [status(thm)], ['19', '26'])).
% 2.82/3.02  thf('28', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 2.82/3.02      inference('demod', [status(thm)], ['14', '27'])).
% 2.82/3.02  thf('29', plain,
% 2.82/3.02      (![X24 : $i, X25 : $i]:
% 2.82/3.02         ((k2_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X24))
% 2.82/3.02           = (k2_xboole_0 @ X24 @ X25))),
% 2.82/3.02      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.82/3.02  thf('30', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 2.82/3.02           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.82/3.02      inference('sup+', [status(thm)], ['28', '29'])).
% 2.82/3.02  thf('31', plain, (![X22 : $i]: ((k2_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 2.82/3.02      inference('cnf', [status(esa)], [t1_boole])).
% 2.82/3.02  thf('32', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((X1) = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.82/3.02      inference('demod', [status(thm)], ['30', '31'])).
% 2.82/3.02  thf('33', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 2.82/3.02           = (X1))),
% 2.82/3.02      inference('demod', [status(thm)], ['7', '32'])).
% 2.82/3.02  thf('34', plain,
% 2.82/3.02      (![X24 : $i, X25 : $i]:
% 2.82/3.02         ((k2_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X24))
% 2.82/3.02           = (k2_xboole_0 @ X24 @ X25))),
% 2.82/3.02      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.82/3.02  thf('35', plain,
% 2.82/3.02      (![X27 : $i, X28 : $i]:
% 2.82/3.02         ((k4_xboole_0 @ (k2_xboole_0 @ X27 @ X28) @ X28)
% 2.82/3.02           = (k4_xboole_0 @ X27 @ X28))),
% 2.82/3.02      inference('cnf', [status(esa)], [t40_xboole_1])).
% 2.82/3.02  thf('36', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 2.82/3.02           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 2.82/3.02      inference('sup+', [status(thm)], ['34', '35'])).
% 2.82/3.02  thf(d5_xboole_0, axiom,
% 2.82/3.02    (![A:$i,B:$i,C:$i]:
% 2.82/3.02     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 2.82/3.02       ( ![D:$i]:
% 2.82/3.02         ( ( r2_hidden @ D @ C ) <=>
% 2.82/3.02           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 2.82/3.02  thf('37', plain,
% 2.82/3.02      (![X5 : $i, X6 : $i, X9 : $i]:
% 2.82/3.02         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 2.82/3.02          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 2.82/3.02          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 2.82/3.02      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.82/3.02  thf('38', plain, (![X26 : $i]: ((k4_xboole_0 @ X26 @ k1_xboole_0) = (X26))),
% 2.82/3.02      inference('cnf', [status(esa)], [t3_boole])).
% 2.82/3.02  thf('39', plain,
% 2.82/3.02      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 2.82/3.02         (~ (r2_hidden @ X8 @ X7)
% 2.82/3.02          | ~ (r2_hidden @ X8 @ X6)
% 2.82/3.02          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 2.82/3.02      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.82/3.02  thf('40', plain,
% 2.82/3.02      (![X5 : $i, X6 : $i, X8 : $i]:
% 2.82/3.02         (~ (r2_hidden @ X8 @ X6)
% 2.82/3.02          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 2.82/3.02      inference('simplify', [status(thm)], ['39'])).
% 2.82/3.02  thf('41', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 2.82/3.02      inference('sup-', [status(thm)], ['38', '40'])).
% 2.82/3.02  thf('42', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 2.82/3.02      inference('condensation', [status(thm)], ['41'])).
% 2.82/3.02  thf('43', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 2.82/3.02          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 2.82/3.02      inference('sup-', [status(thm)], ['37', '42'])).
% 2.82/3.02  thf('44', plain,
% 2.82/3.02      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 2.82/3.02      inference('demod', [status(thm)], ['24', '25'])).
% 2.82/3.02  thf('45', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 2.82/3.02          | ((X1) = (k1_xboole_0)))),
% 2.82/3.02      inference('demod', [status(thm)], ['43', '44'])).
% 2.82/3.02  thf(t3_xboole_0, axiom,
% 2.82/3.02    (![A:$i,B:$i]:
% 2.82/3.02     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 2.82/3.02            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.82/3.02       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.82/3.02            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 2.82/3.02  thf('46', plain,
% 2.82/3.02      (![X11 : $i, X12 : $i]:
% 2.82/3.02         ((r1_xboole_0 @ X11 @ X12) | (r2_hidden @ (sk_C @ X12 @ X11) @ X12))),
% 2.82/3.02      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.82/3.02  thf('47', plain,
% 2.82/3.02      (![X11 : $i, X12 : $i]:
% 2.82/3.02         ((r1_xboole_0 @ X11 @ X12) | (r2_hidden @ (sk_C @ X12 @ X11) @ X11))),
% 2.82/3.02      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.82/3.02  thf('48', plain,
% 2.82/3.02      (![X5 : $i, X6 : $i, X8 : $i]:
% 2.82/3.02         (~ (r2_hidden @ X8 @ X6)
% 2.82/3.02          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 2.82/3.02      inference('simplify', [status(thm)], ['39'])).
% 2.82/3.02  thf('49', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.82/3.02         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 2.82/3.02          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 2.82/3.02      inference('sup-', [status(thm)], ['47', '48'])).
% 2.82/3.02  thf('50', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 2.82/3.02          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 2.82/3.02      inference('sup-', [status(thm)], ['46', '49'])).
% 2.82/3.02  thf('51', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 2.82/3.02      inference('simplify', [status(thm)], ['50'])).
% 2.82/3.02  thf('52', plain,
% 2.82/3.02      (![X11 : $i, X12 : $i]:
% 2.82/3.02         ((r1_xboole_0 @ X11 @ X12) | (r2_hidden @ (sk_C @ X12 @ X11) @ X11))),
% 2.82/3.02      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.82/3.02  thf('53', plain,
% 2.82/3.02      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.82/3.02      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.82/3.02  thf(t4_xboole_0, axiom,
% 2.82/3.02    (![A:$i,B:$i]:
% 2.82/3.02     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 2.82/3.02            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.82/3.02       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.82/3.02            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 2.82/3.02  thf('54', plain,
% 2.82/3.02      (![X15 : $i, X17 : $i, X18 : $i]:
% 2.82/3.02         (~ (r2_hidden @ X17 @ (k3_xboole_0 @ X15 @ X18))
% 2.82/3.02          | ~ (r1_xboole_0 @ X15 @ X18))),
% 2.82/3.02      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.82/3.02  thf('55', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.82/3.02         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 2.82/3.02          | ~ (r1_xboole_0 @ X0 @ X1))),
% 2.82/3.02      inference('sup-', [status(thm)], ['53', '54'])).
% 2.82/3.02  thf('56', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.82/3.02         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 2.82/3.02          | ~ (r1_xboole_0 @ X0 @ X1))),
% 2.82/3.02      inference('sup-', [status(thm)], ['52', '55'])).
% 2.82/3.02  thf('57', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.82/3.02         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X2)),
% 2.82/3.02      inference('sup-', [status(thm)], ['51', '56'])).
% 2.82/3.02  thf('58', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.82/3.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.82/3.02  thf('59', plain,
% 2.82/3.02      (![X27 : $i, X28 : $i]:
% 2.82/3.02         ((k4_xboole_0 @ (k2_xboole_0 @ X27 @ X28) @ X28)
% 2.82/3.02           = (k4_xboole_0 @ X27 @ X28))),
% 2.82/3.02      inference('cnf', [status(esa)], [t40_xboole_1])).
% 2.82/3.02  thf('60', plain,
% 2.82/3.02      (![X24 : $i, X25 : $i]:
% 2.82/3.02         ((k2_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X24))
% 2.82/3.02           = (k2_xboole_0 @ X24 @ X25))),
% 2.82/3.02      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.82/3.02  thf('61', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 2.82/3.02           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.82/3.02      inference('sup+', [status(thm)], ['59', '60'])).
% 2.82/3.02  thf('62', plain,
% 2.82/3.02      (![X24 : $i, X25 : $i]:
% 2.82/3.02         ((k2_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X24))
% 2.82/3.02           = (k2_xboole_0 @ X24 @ X25))),
% 2.82/3.02      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.82/3.02  thf('63', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 2.82/3.02           = (k2_xboole_0 @ X0 @ X1))),
% 2.82/3.02      inference('sup+', [status(thm)], ['61', '62'])).
% 2.82/3.02  thf('64', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 2.82/3.02           = (k2_xboole_0 @ X1 @ X0))),
% 2.82/3.02      inference('sup+', [status(thm)], ['58', '63'])).
% 2.82/3.02  thf('65', plain,
% 2.82/3.02      (![X27 : $i, X28 : $i]:
% 2.82/3.02         ((k4_xboole_0 @ (k2_xboole_0 @ X27 @ X28) @ X28)
% 2.82/3.02           = (k4_xboole_0 @ X27 @ X28))),
% 2.82/3.02      inference('cnf', [status(esa)], [t40_xboole_1])).
% 2.82/3.02  thf('66', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 2.82/3.02           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.82/3.02      inference('sup+', [status(thm)], ['64', '65'])).
% 2.82/3.02  thf('67', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.82/3.02      inference('demod', [status(thm)], ['19', '26'])).
% 2.82/3.02  thf('68', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.82/3.02      inference('demod', [status(thm)], ['66', '67'])).
% 2.82/3.02  thf('69', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 2.82/3.02           = (X1))),
% 2.82/3.02      inference('demod', [status(thm)], ['7', '32'])).
% 2.82/3.02  thf('70', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) @ 
% 2.82/3.02           k1_xboole_0) = (X0))),
% 2.82/3.02      inference('sup+', [status(thm)], ['68', '69'])).
% 2.82/3.02  thf('71', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.82/3.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.82/3.02  thf('72', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.82/3.02      inference('sup+', [status(thm)], ['15', '16'])).
% 2.82/3.02  thf('73', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (X0))),
% 2.82/3.02      inference('demod', [status(thm)], ['70', '71', '72'])).
% 2.82/3.02  thf('74', plain,
% 2.82/3.02      (![X15 : $i, X17 : $i, X18 : $i]:
% 2.82/3.02         (~ (r2_hidden @ X17 @ (k3_xboole_0 @ X15 @ X18))
% 2.82/3.02          | ~ (r1_xboole_0 @ X15 @ X18))),
% 2.82/3.02      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.82/3.02  thf('75', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.82/3.02         (~ (r2_hidden @ X2 @ X0)
% 2.82/3.02          | ~ (r1_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 2.82/3.02      inference('sup-', [status(thm)], ['73', '74'])).
% 2.82/3.02  thf('76', plain,
% 2.82/3.02      (![X1 : $i, X2 : $i, X3 : $i]:
% 2.82/3.02         ~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X1)))),
% 2.82/3.02      inference('sup-', [status(thm)], ['57', '75'])).
% 2.82/3.02  thf('77', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 2.82/3.02      inference('sup-', [status(thm)], ['45', '76'])).
% 2.82/3.02  thf('78', plain,
% 2.82/3.02      (![X29 : $i, X30 : $i]:
% 2.82/3.02         ((k4_xboole_0 @ X29 @ (k3_xboole_0 @ X29 @ X30))
% 2.82/3.02           = (k4_xboole_0 @ X29 @ X30))),
% 2.82/3.02      inference('cnf', [status(esa)], [t47_xboole_1])).
% 2.82/3.02  thf('79', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 2.82/3.02           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.82/3.02      inference('sup+', [status(thm)], ['77', '78'])).
% 2.82/3.02  thf('80', plain, (![X26 : $i]: ((k4_xboole_0 @ X26 @ k1_xboole_0) = (X26))),
% 2.82/3.02      inference('cnf', [status(esa)], [t3_boole])).
% 2.82/3.02  thf('81', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.82/3.02      inference('demod', [status(thm)], ['79', '80'])).
% 2.82/3.02  thf('82', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 2.82/3.02           = (X1))),
% 2.82/3.02      inference('demod', [status(thm)], ['36', '81'])).
% 2.82/3.02  thf('83', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((k4_xboole_0 @ X0 @ 
% 2.82/3.02           (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)))
% 2.82/3.02           = (k3_xboole_0 @ X0 @ X1))),
% 2.82/3.02      inference('sup+', [status(thm)], ['33', '82'])).
% 2.82/3.02  thf('84', plain,
% 2.82/3.02      (![X29 : $i, X30 : $i]:
% 2.82/3.02         ((k4_xboole_0 @ X29 @ (k3_xboole_0 @ X29 @ X30))
% 2.82/3.02           = (k4_xboole_0 @ X29 @ X30))),
% 2.82/3.02      inference('cnf', [status(esa)], [t47_xboole_1])).
% 2.82/3.02  thf('85', plain,
% 2.82/3.02      (![X24 : $i, X25 : $i]:
% 2.82/3.02         ((k2_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X24))
% 2.82/3.02           = (k2_xboole_0 @ X24 @ X25))),
% 2.82/3.02      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.82/3.02  thf('86', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.82/3.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.82/3.02  thf('87', plain,
% 2.82/3.02      (![X27 : $i, X28 : $i]:
% 2.82/3.02         ((k4_xboole_0 @ (k2_xboole_0 @ X27 @ X28) @ X28)
% 2.82/3.02           = (k4_xboole_0 @ X27 @ X28))),
% 2.82/3.02      inference('cnf', [status(esa)], [t40_xboole_1])).
% 2.82/3.02  thf('88', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 2.82/3.02           = (k4_xboole_0 @ X0 @ X1))),
% 2.82/3.02      inference('sup+', [status(thm)], ['86', '87'])).
% 2.82/3.02  thf('89', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 2.82/3.02           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1))),
% 2.82/3.02      inference('sup+', [status(thm)], ['85', '88'])).
% 2.82/3.02  thf('90', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 2.82/3.02           = (k4_xboole_0 @ X0 @ X1))),
% 2.82/3.02      inference('sup+', [status(thm)], ['86', '87'])).
% 2.82/3.02  thf('91', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((k4_xboole_0 @ X0 @ X1)
% 2.82/3.02           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1))),
% 2.82/3.02      inference('demod', [status(thm)], ['89', '90'])).
% 2.82/3.02  thf('92', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 2.82/3.02           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 2.82/3.02      inference('sup+', [status(thm)], ['84', '91'])).
% 2.82/3.02  thf('93', plain,
% 2.82/3.02      (![X29 : $i, X30 : $i]:
% 2.82/3.02         ((k4_xboole_0 @ X29 @ (k3_xboole_0 @ X29 @ X30))
% 2.82/3.02           = (k4_xboole_0 @ X29 @ X30))),
% 2.82/3.02      inference('cnf', [status(esa)], [t47_xboole_1])).
% 2.82/3.02  thf('94', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((k4_xboole_0 @ X1 @ X0)
% 2.82/3.02           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 2.82/3.02      inference('demod', [status(thm)], ['92', '93'])).
% 2.82/3.02  thf('95', plain,
% 2.82/3.02      (![X0 : $i, X1 : $i]:
% 2.82/3.02         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 2.82/3.02           = (k3_xboole_0 @ X0 @ X1))),
% 2.82/3.02      inference('demod', [status(thm)], ['83', '94'])).
% 2.82/3.02  thf('96', plain,
% 2.82/3.02      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.82/3.02      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.82/3.02  thf('97', plain,
% 2.82/3.02      (((k3_xboole_0 @ sk_B @ sk_A) != (k3_xboole_0 @ sk_B @ sk_A))),
% 2.82/3.02      inference('demod', [status(thm)], ['2', '95', '96'])).
% 2.82/3.02  thf('98', plain, ($false), inference('simplify', [status(thm)], ['97'])).
% 2.82/3.02  
% 2.82/3.02  % SZS output end Refutation
% 2.82/3.02  
% 2.82/3.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
